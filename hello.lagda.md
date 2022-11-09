# The classic Hello World, but dependently typed

```
module hello where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
{-# FOREIGN GHC import qualified Data.Text as Text #-}

postulate putStrLn : String → IO ⊤
{-# COMPILE GHC putStrLn = putStrLn . Text.unpack  #-}

postulate _++_ : String → String → String
{-# COMPILE GHC _++_ = Text.append  #-}

record Pair (L R : Set) : Set where
  constructor _×_
  field
    left  : L
    right : R

record Person : Set where
  constructor person_from_
  field
    name     : String
    location : String

data Greeting : Set where
  hello   : Greeting
  goodbye : Greeting

showGreeting : Greeting → String
showGreeting hello   = "Hello"
showGreeting goodbye = "Goodbye,"

showPair : String → Pair String String → String
showPair delim (left × right) = left ++ (delim ++ right)

greet_ : Person → String
greet (person name from _) = showPair " " ((showGreeting hello) × name)


alice = person "Alice" from "Lisbon"

```

Main block...
```
main : IO ⊤
main = do
  putStrLn (greet alice)
```
