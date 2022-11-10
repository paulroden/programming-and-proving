# Chapter 2: Dependent Types

Import the previous chapter
```
open import 01-intro-nat
```

The `Vec` list that knows its length
```
data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : {n : Nat} → A → Vec A n → Vec A (succ n)
```
