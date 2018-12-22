module Main

import Data.Vect
import Util

%default total
%flag C "-g"

data WordState : (guesses : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String)
             -> (missing : Vect letters Char) 
             -> WordState remaining_guesses letters

data Finished : Type where
  Lost : WordState 0 (S letters) -> Finished
  Won  : WordState (S guesses) 0 -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]
  

emptyInputIsNotValid : ValidInput [] -> Void
emptyInputIsNotValid (Letter _) impossible

longInputIsNotValid : ValidInput (x :: (y :: xs)) -> Void
longInputIsNotValid (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No emptyInputIsNotValid
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No longInputIsNotValid

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

partial
readGuess : Nat -> IO (c ** ValidInput c)
readGuess guesses = do putStr $ "Guess[" ++ show guesses ++ "] : "
                       c <- getLine
                       case (isValidString c) of
                          Yes prf => pure (_ ** prf)
                          No contra => do putStrLn "Invalid input"
                                          readGuess guesses


processGuess : (ch : Char) 
            -> WordState  (S guesses) (S chars) 
            -> Either (WordState guesses (S chars)) 
                      (WordState  (S guesses) chars) 
processGuess ch (MkWordState word missing) = case isElem ch missing of
                                                  No contra => Left (MkWordState word missing)
                                                  Yes prf => Right (MkWordState word (removeElem ch missing))
                                                  
partial                                             
game : WordState (S guesses) (S letters) -> IO Finished
game  {guesses} {letters} state 
  = do (_ ** Letter c) <- readGuess guesses
       case processGuess c state of
         Left  l => do putStrLn "Wrong!" 
                       case guesses of 
                         Z   => pure (Lost l)
                         S k => game l
         Right r =>  do putStrLn "Right!"
                        case letters of
                          Z   => pure (Won r)
                          S k => game r

partial                                                    
main : IO ()
main = do result <- game {guesses = 2} (MkWordState "Test" ['T', 'E', 'S'])
          case result of
            Lost (MkWordState word missing) => putStrLn $ "You lost, word is " ++ word
            Won  (MkWordState word missing) => putStrLn $ "You won, word is " ++ word
