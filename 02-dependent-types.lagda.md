# Chapter 2: Dependent Types

Import the previous chapter
```
open import 01-intro-nat
```

The `Vec` list that knows its length, i.e. is an indexed type over its size
```
data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : {n : Nat} → A → Vec A n → Vec A (succ n)
infixr 5 _∷_
```

Zeroes {this feels a bit like numpy}
```
zeroes : (n : Nat) → Vec Nat n
zeroes zero     = []
zeroes (succ n) = 0 ∷ zeroes n

check-zeroes : zeroes 5 ≡ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
check-zeroes = refl
```

Concatenation on size-indexed Vecs (going for a little operator subscript `++ᵥ`, rather than the ungainly `++Vec` used in the text)
```
_++ᵥ_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++ᵥ ys = ys
(x ∷ xs) ++ᵥ ys = x ∷ (xs ++ᵥ ys)

check-++ᵥ : ((1 ∷ 2 ∷ []) ++ (3 ∷ 4 ∷ [])) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
check-++ᵥ = refl
```

Totally heady head
```
head : {A : Set} {n : Nat} → Vec A (succ n) → A
head (x ∷ xs) = x

check-head₂ : head (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 1
check-head₂ = refl

-- #TODO: is there a way to construct a proof that a type cannot be inhabited?
-- check-head₀ : head []
-- check-head₀ ()
```

Self-aware length
```

```

### Exercise 2.1. Implement the functon `downFrom : (n : Nat) → Vec Nat n` that produces the vector whuch 'counts down' from n.
```
downFrom : (n : Nat) → Vec Nat n
downFrom zero     = []
downFrom (succ n) = (succ n) ∷ downFrom n

check-downFromₐ : downFrom 5 ≡ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
check-downFromₐ = refl
```

### Exercise 2.2. Implement `tail` for Vec.
```
tail : {A : Set} {n : Nat} → Vec A (succ n) → Vec A n
tail (x ∷ xs) = xs
```

### Exercise 2.3. Implement a function for the dot product of two `Vec Nat n`s.
```
_∙_ : {n : Nat} → Vec Nat n → Vec Nat n → Nat
[] ∙ [] = 0
(v₀₁ ∷ vs₁) ∙ (v₀₂ ∷ vs₂) = (v₀₁ * v₀₂) + (vs₁ ∙ vs₂)
infix 5 _∙_

check-dotProduct₃ : (2 ∷ 3 ∷ 4 ∷ []) ∙ (3 ∷ 3 ∷ 3 ∷ []) ≡ 27
check-dotProduct₃ = refl

```


## Finite bounded discrete numbers, `Fin`
```
data Fin : Nat → Set where
  zero : {n : Nat} → Fin (succ n)
  succ : {n : Nat} → Fin n → Fin (succ n)
```
But how about a function of `(n : Nat) → Nat → Fin n` to act as a 'constructor' for `Fin`s? (#TODO)

Safe lookup on a `Vec`
```
lookupᵥ : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupᵥ (x ∷ xs) zero     = x
lookupᵥ (x ∷ xs) (succ i) = lookupᵥ xs i

0₃ : Fin 3
0₃ = zero

2₃ : Fin 3
2₃ = succ (succ zero)

2₄ : Fin 4
2₄ = succ (succ zero)

lookupᵥ-check₃ : (lookupᵥ (4 ∷ 5 ∷ 6 ∷ []) 2₃) ≡ 6
lookupᵥ-check₃ = refl

-- #TODO: again, some kind of "this is not possible" proof here
-- lookupᵥ-check₄ : (lookupᵥ (4 ∷ 5 ∷ 6 ∷ []) 2₄) ≡ 6
-- lookupᵥ-check₄ = refl

```

### Exercise 2.4. Implement a function which sets a value at a particular position in the `Vec` and returns the `Vec` with that changed and all other elements as before.
```
putᵥ : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putᵥ zero     x′ (x ∷ xs) = x′ ∷ xs
putᵥ (succ n) x′ (x ∷ xs) = x  ∷ (putᵥ n x′ xs)

check-putᵥ : putᵥ 2₄ 210 (10 ∷ 11 ∷ 12 ∷ 13 ∷ []) ≡ (10 ∷ 11 ∷ 210 ∷ 13 ∷ [])
check-putᵥ = refl
```
