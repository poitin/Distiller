module Main (
    main
) where

import Exception
import Term
import Trans
import Helpers

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
