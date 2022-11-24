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

-- The head of and empty list is impossible! This cannot typecheck.
check-head₀ : head [] → ⊥
check-head₀ ()
```

Self-aware length
```
lengthᵥ : {A : Set} {n : Nat} → Vec A n → Nat
lengthᵥ {_} {n} _ = n

check-lengthᵥ : lengthᵥ (0 ∷ 0 ∷ 0 ∷ 0 ∷ []) ≡ 4
check-lengthᵥ = refl
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

Safe lookup on a `Vec`
```
lookupᵥ : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupᵥ (x ∷ xs) zero     = x
lookupᵥ (x ∷ xs) (succ i) = lookupᵥ xs i

0₃ : Fin 3
0₃ = zero

2₃ : Fin 3
2₃ = succ (succ zero)

lookupᵥ-check₃ : (lookupᵥ (4 ∷ 5 ∷ 6 ∷ []) 2₃) ≡ 6
lookupᵥ-check₃ = refl

2₄ : Fin 4
2₄ = succ (succ zero)

3₄ : Fin 4
3₄ = succ (succ (succ zero))

-- this does not typecheck; Agda complains that we are using a `Fin 4`, not a `Fin 3` for the lookup
lookupᵥ-check₄ : ((lookupᵥ (4 ∷ 5 ∷ 6 ∷ []) 2₄) ≡ 6) → ⊥
lookupᵥ-check₄ ()
```

### Exercise 2.4. Implement a function which sets a value at a particular position in the `Vec` and returns the `Vec` with that changed and all other elements as before.
```
putᵥ : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putᵥ zero     x′ (x ∷ xs) = x′ ∷ xs
putᵥ (succ n) x′ (x ∷ xs) = x  ∷ (putᵥ n x′ xs)

check-putᵥ : putᵥ 2₄ 210 (10 ∷ 11 ∷ 12 ∷ 13 ∷ []) ≡ (10 ∷ 11 ∷ 210 ∷ 13 ∷ [])
check-putᵥ = refl
```
_figuring this out was fun! -- case-split on `Fin n` and there's only one sensible way to make it work ⌣_

## Dependent pairs 🍎×🍐
The sigma type: a dependent pair where the type of right/second member of the pair depends on the left/first:
```
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

_×′_ : (A B : Set) → Set
A ×′ B = Σ A (λ _ → B)

exlΣ : {A : Set} {B : A → Set} → Σ A B → A
exlΣ (l , r) = l

exrΣ : {A : Set} {B : A → Set} → (z : Σ A B) → B (exlΣ z)
exrΣ (l , r) = r

```


Exercise 2.5. Implement functions converting back and forth between `A × B` and `A ×′ B`.
```
fromΣ : {A : Set} {B : A → Set} → (z : Σ A B) → (A × B (exlΣ z))
fromΣ (l , r) = (l , r)

toΣ : {A B : Set} → (A × B) → (A ×′ B)
toΣ (l , r) = l , r
```


For an example of a sigma type is a list with its length provided in its type:
```
List′ : (A : Set) → Set
List′ A = Σ Nat (Vec A)
-- note that the argument `A` _is_ a type here.

listNil : {A : Set} → List′ A
listNil = 0 , []

list3 : {A : Set} → A → A → A → List′ A
list3 a b c = 3 , (a ∷ b ∷ c ∷ [])

```

### Exercise 2.6. Implement functions converting back and forth between `List A` and `List′ A`.
First define:
```
-- the 'sigma typed' empty list is a list parameterised by a length of zero
[]′ : {A : Set} → List′ A
[]′ = 0 , []

-- appending to a 'sigma typed' list, indexed over some n ∈ ℕ, just means taking the successor of the index n
_∷′_ : {A : Set} → A → List′ A → List′ A
x ∷′ (n , xs) = succ n , x ∷ xs

-- to a 'sigma typed' list
toList′ : {A : Set} → List A → List′ A
toList′ [] = []′
toList′ (x ∷ xs) = x ∷′ toList′ xs

-- from a 'sigma typed' list
fromList′ : {A : Set} → List′ A → List A
fromList′ (zero   , []      ) = []
fromList′ (succ n , (x ∷ xs)) = x ∷ fromList′ (n , xs)
```
