module Main

import Printf

main : IO ()
main = putStr $ format "this is the %d time I am using format with %s and  %s\n" 1 "Int" "String"

