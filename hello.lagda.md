# The classic Hello World, but dependently typed

```
module hello where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC putStrLn = putStrLn . Text.unpack  #-}

main : IO ⊤
main = putStrLn "Hello world!"

```


