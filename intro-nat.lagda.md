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

## Exercise 1.1: define the function `halve : Nat → Nat` that computes the result of diviging by two:
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

check₀ : halve 0 ≡ 0
check₀ = refl

check₁ : halve 1 ≡ 0
check₁ = refl

check₃ : halve 3 ≡ 1
check₃ = refl

check₆ : halve 6 ≡ 3
check₆ = refl

checkₓ : halve 6 ≡ 2
checkₓ = {!!}

```

   

```
double : Nat → Nat
double zero = zero
double (succ n) = succ (succ n)

```

