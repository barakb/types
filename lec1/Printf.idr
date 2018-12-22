module Printf

{-
 * Enumerated Types
 * Union Types
 * Recursive Types
 * Generic Types
 * Dependent types
-}



data DayOfWeek = Sun | Mon |Tue

||| This is the fuction that I just wrote
||| * This is markdown line 1
||| * This is markdown line 1
||| @d is the current day of the week
nextDay : (d: DayOfWeek) -> DayOfWeek
nextDay Sun = Mon
nextDay Mon = Tue
nextDay Tue = Sun


IntOrString : Bool -> Type
IntOrString False = Int
IntOrString True = String

getIntOrString : (b: Bool) -> IntOrString b
getIntOrString False = 0
getIntOrString True = "0"

-- "%d This is not the same as %s\n"
public export
data FormatString = Str FormatString
                  | Num FormatString
                  | Literal String FormatString
                  | End
public export           
parse : String -> FormatString
parse str = parse' (unpack str)
  where
    parse' : List Char -> FormatString
    parse' [] = End
    parse' ('%' :: 'd' :: xs) = Num (parse' xs)
    parse' ('%' :: 's':: xs) = Str (parse' xs) 
    parse' (x :: xs) = case (parse' xs) of
                            (Literal str rest) => Literal (strCons x str) rest
                            parsed => Literal (cast x) parsed
                            
public export
TypeOfFormat : FormatString -> Type
TypeOfFormat (Str rest) = String -> TypeOfFormat rest
TypeOfFormat (Num rest) = Int -> TypeOfFormat rest
TypeOfFormat (Literal x rest) = TypeOfFormat rest
TypeOfFormat End = String

public export
format : (s : String) -> TypeOfFormat (parse s)
format s = format' (parse s) ""
  where 
     format' : (fmt : FormatString) -> (buf : String) -> TypeOfFormat fmt
     format' (Str rest) buf = \st => format' rest (buf ++ st)
     format' (Num rest) buf = \n => format' rest (buf ++ (cast n))
     format' (Literal str rest) buf = format' rest (buf ++ str)
     format' End buf = buf

