{-
An interpreter for Eodermdrome (https://esolangs.org/wiki/Eodermdrome).

Usage: let Right prog = parse programParser "" "thequickbrownfox (Hello world!\n) thou"
       in fromMaybe "" =<< unfoldr (step prog) (initialState, "input...")


Known issues
----
The code is poorly tested and probably has some bugs.
This is partly due to the scarcity of Eodermdrome programs.

No debugging features in main. However, the internal functions
(findMatch, replaceMatch, etc.) allow access to the internal state.

The punctuated-whitespace syntax is not recognised.

The rules are matched using brute force search. Low-hanging improvements:
 - prune the search (eg. Ullmann 1976);
 - remember which rules and parts of the state matched recently.

The interpreter tries rules with no input sets first, so that it does not
read the input unnecessarily. If the program is nondeterministic, this
might starve rules with input sets.
The interpreter will also not halt if it is blocked on input, even if
no rules would match. Fixing this requires concurrency.


Legalese
----
This program is in the public domain.
-}

{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Monad
import Control.Applicative ((<$>))
import Control.Arrow
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Parsec

import System.IO
import System.Environment
import System.Exit


{- Utilities -}

type Graph label = M.Map Int (label, S.Set Int)

emptyGraph = M.empty

graphNumNodes g = M.size g
graphNodes g = [ (k, l) | (k, (l, _)) <- M.toList g ]
graphEdges g = [ (u, v) | (u, (_, vs)) <- M.toList g, v <- S.toList vs ]
neighbours g v = snd (g M.! v)
degreeOf g v = S.size (neighbours g v)
labelOf g v = fst (g M.! v)
adjacent g u v = S.member u (snd (g M.! v))
findLabel g l = M.keys (M.filter ((l==) . fst) g)

insertNode (v, l) g = M.insert v (l, S.empty) g
deleteNode v g = S.foldl' (\g u -> M.update (Just . second (S.delete v)) u g) (M.delete v g) (neighbours g v)
insertEdge u v g = M.update (Just . second (S.insert u)) v . M.update (Just . second (S.insert v)) u $ g
deleteEdge u v g = M.update (Just . second (S.delete u)) v . M.update (Just . second (S.delete v)) u $ g
newNode l g = let v = maybe 0 (succ.fst.fst) (M.maxViewWithKey g)
              in (v, insertNode (v, l) g)
setLabel v l g = M.update (Just . first (const l)) v g
graphMapLabels = M.map . first


{- Interpreter -}

-- the labels of open nodes refer to each other, closed nodes have Nothing
type MatchGraph = Graph (Char, Maybe Int)
data Rule = Rule (Maybe (S.Set Char)) MatchGraph (Maybe String) MatchGraph
  deriving Show

-- NB: findMatch assumes that pat has node numbers [0..graphSize pat-1]
--     and the subgraph pat[0..i] is connected for all i.
findMatch :: Graph a -> MatchGraph -> [M.Map Int Int]
findMatch gr pat = do
  let pv0 = 0
      (_, isNothing -> closed) = labelOf pat pv0
  (v0, _) <- graphNodes gr
  guard $ (if closed then (==) else (>=)) (degreeOf gr v0) (degreeOf pat pv0)
  search (pv0, v0) (M.singleton pv0 v0) (M.singleton v0 pv0)
 where
  search (pv, v) whichPat whichGr
    | M.size whichPat == graphNumNodes pat = return whichPat
    | otherwise = do
        let pv' = pv + 1
            (_, isNothing -> closed) = labelOf pat pv'
            pvJoin = fst . fromJust $ S.minView (neighbours pat pv')
            vJoin = whichPat M.! pvJoin
        v' <- S.toList $ neighbours gr vJoin
        guard $ M.notMember v' whichGr
        guard $ (if closed then (==) else (>=)) (degreeOf gr v') (degreeOf pat pv')
        guard $ and [ maybe True (adjacent gr v') (M.lookup pvn whichPat)
                      | pvn <- S.toList (neighbours pat pv') ]
        search (pv', v') (M.insert pv' v' whichPat) (M.insert v' pv' whichGr)

replaceMatch :: Graph Char -> Rule -> M.Map Int Int -> Graph Char
replaceMatch gr (Rule _ pat _ replacement) match =
  -- follows steps 3..6 in the language spec
  (foldl' (flip $ uncurry deleteEdge) `flip` [ (match M.! u, match M.! v) | (u, v) <- graphEdges pat ]) >>>
  (foldl' (flip deleteNode) `flip` [ match M.! v | (v, (_, Nothing)) <- graphNodes pat ]) >>>
  (\gr -> mapAccumL (\gr (v, l) -> let (v', gr') = newNode l gr in (gr', (v, v'))) gr
                    [ (v, l) | (v, (l, Nothing)) <- graphNodes replacement ]) >>>
  (\(gr, newvs) ->
     let repmatch = M.fromList $ newvs ++ [ (v, match M.! pv) | (v, (_, Just pv)) <- graphNodes replacement ]
     in foldl' (flip $ uncurry insertEdge) gr [ (repmatch M.! u, repmatch M.! v) | (u, v) <- graphEdges replacement ])
    $ gr

step :: [Rule] -> (Graph Char, String) -> Maybe (Maybe String, (Graph Char, String))
step rules (gr, input) =
  -- NB: rely on laziness to not read the input if a no-input rule could fire
  let readyRules = noInputRules ++ readyInputRules
        where (noInputRules, inputRules) = partition (\(Rule inputSpec _ _ _) -> isNothing inputSpec) rules
              readyInputRules = filter (\(Rule inputSpec _ _ _) -> maybe undefined ready inputSpec) inputRules
              ready inputChars = maybe False (`S.member` inputChars) (listToMaybe input)
  in case listToMaybe $ concat [ map ((,) rule) (findMatch gr pat)
                                 | rule@(Rule _ pat _ _) <- readyRules ] of
       Nothing -> Nothing
       Just (rule, match) ->
         let gr' = replaceMatch gr rule match
             Rule inputSpec _ outputSpec _ = rule
         in Just (outputSpec, (gr', if isJust inputSpec then drop 1 input else input))

-- NB: assigns node numbers from the sequence [0..] (needed by findMatch)
readGraph cs@(c:_) = mk (insertNode (0, c) emptyGraph) (M.singleton c 0) 0 cs
  where mk gr m _ [c] = if M.member c m then gr else snd $ newNode c gr
        mk gr m v0 (c0:c:cs) =
          let (v, m', gr') =
                case M.lookup c m of
                  Just v -> (v, m, gr)
                  Nothing -> let (v, gr') = newNode c gr in (v, M.insert c v m, gr')
          in mk (insertEdge v0 v gr') m' v (c:cs)


{- Parsers -}

eodeSpace = do
  spaces
  many $ do char ','; anyChar `manyTill` char ','; spaces
  return ()

ruleParser = do
  let ioSpec = option Nothing $ do
        char '('
        c <- anyChar
        cs <- anyChar `manyTill` char ')'
        eodeSpace
        return $ Just (c:cs)

  input <- ioSpec

  matchSpec <- many1 letter
  eodeSpace
  let matchGraph0 = readGraph matchSpec

  output <- ioSpec

  replaceSpec <- many1 letter
  eodeSpace
  let replaceGraph0 = readGraph replaceSpec
      matchGraph = (`graphMapLabels` matchGraph0) $ \c ->
                     (c, listToMaybe (findLabel replaceGraph0 c))
      replaceGraph = (`graphMapLabels` replaceGraph0) $ \c ->
                       (c, listToMaybe (findLabel matchGraph0 c))

  return $ Rule (S.fromList <$> input) matchGraph output replaceGraph

programParser = do
  eodeSpace;
  rules <- many1 ruleParser
  eof
  return rules


{- main -}

initialState = readGraph "thequickbrownfoxjumpsoverthelazydog"

main = do
  mapM_ (`hSetBuffering` NoBuffering) [stdin, stdout]

  args <- getArgs
  when (length args /= 1 || head args `elem` ["-h", "--help"]) $
    do prog <- getProgName
       hPutStrLn stderr $ "Usage: " ++ prog ++ " program.eode"
       exitFailure
  prog <- readFile (head args)
  case parse programParser (head args) prog of
    Left err -> hPrint stderr err >> exitFailure
    Right rules -> do
      input <- getContents
      putStr $ fromMaybe "" =<< unfoldr (step rules) (initialState, input)
