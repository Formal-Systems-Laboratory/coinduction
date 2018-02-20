import Data.Char

{- Removes Coq's (* ... *) comments.
   Replaces with a single newline if the
   comment contained any *) -}

uncomment [] = []
uncomment ('(':'*':s) = incomment False s
  where incomment line ('*':')':s) = (if line then "\n" else "")++uncomment s
        incomment _ ('\n':s) = incomment True s
        incomment line (c:s) = incomment line s
uncomment (c:s) = c:uncomment s

main = interact uncomment
