# Chapter 01 – Introduction

Put this in a module for subsequent chapters to import.
```
module 01-intro-nat where
```

Start by defining natural numbers, in the classical Peano way:
```
data Nat : Set where
  zero : Nat
  succ : Nat → Nat
```

Then define addition on the natural numbers
```
_+_ : Nat → Nat → Nat
zero     + m = m
(succ n) + m = succ (n + m)
```
... and (bounded) subtraction, which we'll need later (cf. 'monus' in PLFA)
```
_-_ : Nat → Nat → Nat
n        - zero     = n
zero     - (succ n) = zero
(succ n) - (succ m) = n - m
```

### Exercise 1.1: define the function `halve : Nat → Nat` that computes the result of dividing by two.
```
halve : Nat → Nat
halve zero            = zero
halve (succ zero)     = zero
halve (succ (succ n)) = succ (halve n)
```

Let's try a few tests, using more convenient notation…
```
{-# BUILTIN NATURAL Nat #-}

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where
  -- no constructors

absurd : {A : Set} → ⊥ → A
absurd ()

¬_ : Set → Set
¬ A = A → ⊥
infix 3 ¬_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

check-halve₀ : halve 0 ≡ 0
check-halve₀ = refl

check-halve₁ : halve 1 ≡ 0
check-halve₁ = refl

check-halve₃ : halve 3 ≡ 1
check-halve₃ = refl

check-halve₆ : halve 6 ≡ 3
check-halve₆ = refl

check-halve-big : halve 10000 ≡ 5000
check-halve-big = refl

check-halveₓ : halve 6 ≢ 2
check-halveₓ = λ ()

```

   
### Excercise 1.2: define the function `_*_ : Nat → Nat → Nat` for multiplication of two natural numbers.
We already have addition on ℕ with `_+_` so:
```
_*_ : Nat → Nat → Nat
zero     * m = zero
(succ n) * m = m + (n * m)

check-*-zero : (1 * 0) ≡ 0
check-*-zero = refl

check-*-ten : (10 * 2) ≡ (5 * 4)
check-*-ten = refl
```

### Excercise 1.3: Define the type `Bool` with constructors `true` and `false` and define logical negation, conjunction, and disjunction by pattern matching.
First, the bools:
```
data Bool : Set where
  true  : Bool
  false : Bool 
```
Then tie a not:
```
not_ : Bool → Bool
not true  = false
not false = true
```
And conjunction:
```
_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false
```
Or disjunction:
```
_||_ : Bool → Bool → Bool
true  || b = true
false || b = b
```

# Moving on with polymorphism
Polymorphic identity
```
id : {A : Set} → A → A
id x = x
```
Ternary conditional
```
if_then_else : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y
```

Lists & Pairs
```
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
infixr 5 _∷_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

exl : {A B : Set} → A × B → A
exl (l , r) = l

exr : {A B : Set} → A × B → B
exr (l , r) = r
```

### Exercise 1.4. Implement:
 - `length : {A : Set} → List A → Nat`
 - `_++_ : {A : Set} → List A → List A → List A`
 - `map : {A B : Set} → (A → B) → List A → List B`

length
```
length : {A : Set} → List A → Nat
length []       = zero
length (x ∷ xs) = succ (length xs)

check-length₀ : length {Nat} [] ≡ 0  -- note a type needs to be provided here
check-length₀ = refl

check-length₃ : length (10 ∷ 20 ∷ 30 ∷ []) ≡ 3
check-length₃ = refl
```

concatenation ++
```
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

check-concat-length :
  length ( (11 ∷ 12 ∷ 13 ∷ []) ++ (21 ∷ 22 ∷ []) )
  ≡ 5
check-concat-length = refl
```

map
```
map : {A B : Set} → (A → B) → List A → List B
map _ []       = []
map f (x ∷ xs) = f x ∷ (map f xs)

check-map : map (λ x → 3 * x) (1 ∷ 2 ∷ 3 ∷ []) ≡ (3 ∷ 6 ∷ 9 ∷ [])
check-map = refl
```

### Exercise 1.5. Implement the type `Maybe A`. Then, implement a list lookup function that returns a `Maybe A` for any `List A`.
```
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup []       _        = nothing
lookup (x ∷ _ ) zero     = just x
lookup (x ∷ xs) (succ n) = lookup xs n


check-lookup₀ : lookup (3 ∷ 6 ∷ 9 ∷ []) 0 ≡ just 3
check-lookup₀ = refl

check-lookup₂ : lookup (3 ∷ 6 ∷ 9 ∷ []) 2 ≡ just 9
check-lookup₂ = refl

check-lookupₓ : lookup (3 ∷ 6 ∷ 9 ∷ []) 10 ≡ nothing
check-lookupₓ = refl
```

### Exercise 1.6. Is it possible to implement a function of type `{A : Set} → List A → Nat → A` in Agda?
No. Because all cases of `Nat` need to be handled, otherwise the function is not complete. Since ℕ is an infinite set, there for any `List A`, there exists some `x ∈ ℕ` beyond the length of the list (i.e. `succ (length list)`). If a bounded set of `Nat`s were used, a function returning an `A` could be created.


