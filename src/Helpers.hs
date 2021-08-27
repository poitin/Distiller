module Helpers where

import Exception
import Term
import Trans

import Text.ParserCombinators.Parsec
import Debug.Trace
import System.Directory
import System.IO
import Control.Monad
import Data.List
import System.Exit
import System.Process

evalProg :: (Num c, Foldable t) => [[Char]] -> Term -> [(String, (t String, Term))] -> IO (Term, Int, c)
evalProg [] t d = do let (v,r,a) = eval t EmptyCtx d 0 0
                     return (v, r, a)
evalProg (x:xs) t d = do putStr (x++" = ")
                         hFlush stdout
                         l <-  getLine
                         case parseTerm l of
                            Left s -> do putStrLn ("Could not parse term: "++ show s)
                                         evalProg (x:xs) t d
                            Right u -> evalProg xs (subst u (abstract t x)) d


loadProg :: [[Char]] -> [[Char]] -> [(String, ([String], Term))] -> Maybe [Char] -> IO (Maybe (Term, [([Char], ([String], Term))]))
loadProg [] _ d _ = return (Just (makeProg d))
loadProg (x:xs) ys d sourcesDir = do
  if  x `elem` ys
    then loadProg xs ys d sourcesDir
    else case sourcesDir of
        Nothing -> do
              r <- loadFile x
              case r of
                 Nothing -> return Nothing
                 Just (fs,d') -> loadProg (xs++fs) (x:ys) (d++d') sourcesDir
        Just sourcesDir' -> do
              r <- loadFile (sourcesDir' ++ x)
              case r of
                 Nothing -> return Nothing
                 Just (fs,d') -> loadProg (xs++fs) (x:ys) (d++d') sourcesDir

loadFile :: String -> IO (Maybe ([String],[(String,([String],Term))]))
loadFile f = do x <-  doesFileExist (f++".pot")
                if   x
                     then do putStrLn ("Loading file: "++f++".pot")
                             c <-  readFile (f++".pot")
                             case parseModule c of
                                Left s -> do putStrLn ("Could not parse program in file "++f++".pot: "++ show s)
                                             return Nothing
                                Right t -> return (Just t)
                     else do putStrLn ("No such file: "++f++".pot")
                             return Nothing