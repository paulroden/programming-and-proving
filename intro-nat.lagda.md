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

### Exercise 1.1: define the function `halve : Nat → Nat` that computes the result of diviging by two.
```
halve : Nat → Nat
halve zero                   = zero
halve (succ zero)            = zero
halve (succ (succ n))        = succ (halve n)
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

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

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

check-halveₓ : halve 6 ≡ 2
check-halveₓ = {!!}  -- #TODO: assert absurdness here

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
