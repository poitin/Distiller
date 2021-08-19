module Main (
    main
) where

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

data Command = Load String (Maybe String)
             | Prog
             | Term
             | Eval
             | Distill (Maybe String)
             | Quit
             | Help
             | Unknown

command str = let res = words str
              in case res of
                   [":load",f] -> Load f (Nothing)
                   [":load",f, sourceDir] -> Load f (Just sourceDir)
                   [":prog"] -> Prog
                   [":term"] -> Term
                   [":eval"] -> Eval
                   [":distill"] -> Distill Nothing
                   [":distill", f] -> Distill (Just f)
                   [":quit"] -> Quit
                   [":help"] -> Help
                   _ -> Unknown

helpMessage = "\n:load filename directory\t\tTo load the given filename with imports stored in directory\n"++
               ":prog\t\t\tTo print the current program\n"++
               ":term\t\t\tTo print the current term\n"++
               ":eval\t\t\tTo evaluate the current program\n"++
               ":distill <filename>\t\tTo distill the current program. If the file name is provided, the distillation result will be stored in the specified file.\n"++
               ":quit\t\t\tTo quit\n"++
               ":help\t\t\tTo print this message\n"


-- Entry point for main program

main = toplevel Nothing

toplevel :: Maybe Prog -> IO ()
toplevel p = do putStr "POT> "
                hFlush stdout
                x <-  getLine
                case command x of
                   Load f sourcesDir -> do
                     prog <- loadProg [f] [] [] sourcesDir
                     toplevel prog
                   Prog -> case p of
                              Nothing -> do putStrLn "No program loaded"
                                            toplevel p
                              Just (t,d) -> do putStrLn (showProg (t,d))
                                               toplevel p
                   Term -> case p of
                              Nothing -> do putStrLn "No program loaded"
                                            toplevel p
                              Just (t,d) -> do print t 
                                               toplevel p
                   Eval -> case p of
                              Nothing -> do putStrLn "No program loaded"
                                            toplevel p
                              Just (t,d) -> do 
                                (v, r, a) <- evalProg (free t) t d
                                print v
                                putStrLn ("Reductions: " ++ show r)
                                putStrLn ("Allocations: " ++ show a)
                                toplevel p
                   Distill f -> case p of
                                     Nothing -> do putStrLn "No program loaded"
                                                   toplevel p
                                     Just (t,d) -> do let p' = dist (t,d)
                                                      putStrLn (showProg p')
                                                      case f of
                                                           Nothing -> return ()
                                                           Just f -> writeFile f (showProg p')  
                                                      toplevel (Just p')
                   Quit -> return ()
                   Help -> do putStrLn helpMessage
                              toplevel p
                   Unknown -> do putStrLn "Err: Could not parse command, type ':help' for a list of commands"
                                 toplevel p

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
