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

data Command = Load String
             | Prog
             | Term
             | Eval
             | Distill (Maybe String)
             | Quit
             | Help
             | Unknown

command str = let res = words str
              in case res of
                   [":load",f] -> Load f
                   [":prog"] -> Prog
                   [":term"] -> Term
                   [":eval"] -> Eval
                   [":distill"] -> Distill Nothing
                   [":distill", f] -> Distill (Just f)
                   [":quit"] -> Quit
                   [":help"] -> Help
                   _ -> Unknown

helpMessage = "\n:load filename\t\tTo load the given filename\n"++
               ":prog\t\t\tTo print the current program\n"++
               ":term\t\t\tTo print the current term\n"++
               ":eval\t\t\tTo evaluate the current program\n"++
               ":distill <filename>\t\tTo distill the current program. If file name provided, deistillation result will be stored to the specified file.\n"++
               ":quit\t\t\tTo quit\n"++
               ":help\t\t\tTo print this message\n"


-- Entry point for main program

main = toplevel Nothing

toplevel :: Maybe Prog -> IO ()
toplevel p = do putStr "POT> "
                hFlush stdout
                x <-  getLine
                case command x of
                   Load f -> g [f] [] []
                             where
                             g [] ys d = toplevel (Just (makeProg d))
                             g (x:xs) ys d = if   x `elem` ys
                                             then g xs ys d
                                             else do r <- loadFile x
                                                     case r of
                                                        Nothing -> toplevel Nothing
                                                        Just (fs,d') -> g (xs++fs) (x:ys) (d++d')
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
                              Just (t,d) -> f (free t) t
                                            where
                                            f [] t = do let (v,r,a) = eval t EmptyCtx d 0 0
                                                        print v
                                                        putStrLn ("Reductions: " ++ show r)
                                                        putStrLn ("Allocations: " ++ show a)
                                                        toplevel p
                                            f (x:xs) t = do putStr (x++" = ")
                                                            hFlush stdout
                                                            l <-  getLine
                                                            case parseTerm l of
                                                               Left s -> do putStrLn ("Could not parse term: "++ show s)
                                                                            f (x:xs) t
                                                               Right u -> f xs (subst u (abstract t x))
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
