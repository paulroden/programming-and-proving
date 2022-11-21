# Chapter 3: The Curry-Howard Correspondence

This is where types become propositions, and propositions become proofs.
The proposition corresponding to "truth" was used in Chapter 1, but let's revisit it here (rather than reimporting). Truth is really called "top" and also responds to being called 'the unit type'. 
```
data ⊤ : Set where
  tt : ⊤
```
and if there is a truth, there should be a false. Hood? Ity?
```
data ⊥ : Set where
  -- no constructors
```
that last sentence was not possible to construct beause there are constructors for falsity. Also known as "bottom".
Since falsity is akin to lying, and lying gives a person the power to say anything, so the bottom type can make an _absurd_ proof of anything we like (as the people of Latinland would say "ex falso quodlibet").
```
absurd : {A : Set} → ⊥ → A
absurd ()
```

Boolean values will be useful later, but remember, ⊤ and ⊥ are _types_, while `true` and `false` are _values_.
```
data Bool : Set where
  true  : Bool
  false : Bool

not_ : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

_||_ : Bool → Bool → Bool
true  || _ = true
false || b = b

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

¬_ : Set → Set
¬ A = A → ⊥
infix 3 ¬_

-- we'll also need the plain pair type, since it corresponds to logical conjunction
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

exl : {A B : Set} → A × B → A
exl (l , r) = l

exr : {A B : Set} → A × B → B
exr (l , r) = r



```


### Exercise 3.1. Define the `Either` type in Agda, and write down a definition of the function:
`cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C`
```
data Either (A : Set) (B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left  x) f g = f x
cases (right x) f g = g x
```

```
curry : {A B C : Set} → ((A × B) → C) → A → B → C
curry f x y = f (x , y)

uncurry : {A B C : Set} → (A → B → C) → ((A × B) → C)
uncurry f (x , y) = f x y

```



### Exercise 3.2.
```
-- 1. If `A` then `B` implies `A`.
ifA : {A B : Set} → A → (B → A)
ifA = λ x _ → x

-- 2. If (`A` and `true`) then (`A` or `false`).
ifA-and : {A : Set} → (A × ⊤) → Either A ⊥
ifA-and (l , r) = left l

-- 3. If `A` implies (`B` implies `C`), then (`A` and `B`) implies `C`.
ifA⇒BC-then : {A B C : Set} → A → (B → C) → (A × (B → C)) -- (A × B) → C
ifA⇒BC-then x f = x , (λ z → f z)
-- this checks as a solution for " If `A` implies (`B` implies `C`), then
-- (`A` and (`B` implies `C`).", which is not exactly what the specificaton
-- was. Is this the correct interpretation of the exercise?
-- #TODO: revisit,` ⋯ → (A × (B → C))` vs. `‌⋯ → (A × B) → C`

-- 4. If A and (B or C), then either (A and B) or (A and C).
ifA-and-BC-then : {A B C : Set} → (A × Either B C) → Either (A × B) (A × C)
ifA-and-BC-then (a , left  b|c) = left  (a , b|c)
ifA-and-BC-then (a , right b|c) = right (a , b|c)


-- 5. If `A` implies `C` and `B` implies `D`, then (`A` and `B`) implies (`C` and `D`).
ifA⇒B-and-B⇒D-then : {A B C D : Set} → ((A → C) × (B → D)) → ((A × B) → (C × D))
ifA⇒B-and-B⇒D-then (f , g) = λ x → ((λ y → f y) (exl x)), ((λ z → g z) (exr x))
```

Exercise 3.3. Write a function of type `{P : Set} → (Either P (P → ⊥) → ⊥) → ⊥ `
```
classicalMiddle : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
classicalMiddle = λ x₁ → x₁ (right (λ x₀ → x₁ (left x₀)))
-- #TODO: revisit -- how does this work; should it involve some ¬ (¬ x)?
-- note that `{P : Set} → Either P (P → ⊥)` is the 'excluded middle' for P
-- see: https://plfa.github.io/Negation/#excluded-middle-is-irrefutable
```

Aside on the "Excluded middle is irrefutable" section in PLFA (and the Agda StdLib) #TODO: revisit
```
open import Level using (Level; _⊔_)

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

infixr 1 _⊎_

data _⊎_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B
  
classicalMiddle′ : {P : Set} → ¬ ¬ (A ⊎ ¬ A)  -- ¬ ¬ (P × (¬ P)) → ⊥
classicalMiddle′ = λ x₁ → x₁ (inj₂ (λ x₀ → x₁ (inj₁ x₀)))
```


## Predicate Logic
We can define a proposition expressing whether a natural number, `n` is even. Since propositions _are_ types, this propisition can be expressed as:
```
open import 01-intro-nat using (Nat; zero; succ)

data NatIsEven : Nat → Set where
  even-zero : NatIsEven zero
  even-suc2 : {n : Nat} → NatIsEven n → NatIsEven (succ (succ n))
```

This lets us prove that, say, 6 is even:
```
6-is-even : NatIsEven 6
6-is-even = even-suc2 (even-suc2 (even-suc2 even-zero))
```
and that there is not a proof that 7 is even (careful with the wording here, as we are not using classical logic!). The below _implies_ that this proposition is false.
```
7-is-even : NatIsEven 7 → ⊥
7-is-even (even-suc2 (even-suc2 (even-suc2 ())))
```

It is useful to define a predicate to express that a predicate, which results in a `Bool` is true:
```
data IsTrue : Bool → Set where
  is-true : IsTrue true
```

Applying this to the a plain (non-type-indexed) list as defined in the first chapter, it is possible to prove that its length is, well, what its length should be:
```
open import 01-intro-nat using (List; _∷_; []; length)


_=ℕ_ : Nat → Nat → Bool
zero     =ℕ zero     = true
(succ n) =ℕ (succ m) = n =ℕ m
{-# CATCHALL #-}
_        =ℕ _        = false


length-is-3 : IsTrue (length (1 ∷ 2 ∷ 3 ∷ []) =ℕ 3)
length-is-3 = is-true
```

Nice.
How about proving that doubling any natural number will always result in an even number:
```
double_ : Nat → Nat
double zero   = zero
double succ n = succ (succ (double n))

double-is-always-even : (n : Nat) → NatIsEven (double n)
double-is-always-even zero     = even-zero
double-is-always-even (succ n) = even-suc2 (double-is-always-even n)
```
(⇧ and that proof was completed entiredy with Agda's constraint solver, other than changing its default `x` to `n`!)


Next, an inductive proof that for any natural number `n`, ` n =ℕ n` is true:
```
n-equals-n : (n : Nat) → IsTrue (n =ℕ n)
n-equals-n zero     = is-true
n-equals-n (succ n) = n-equals-n n
```

Now, given that an sigma-type corresponds to an existential statement (of the form of "there exists some ... such that ..."), we can construct proofs that certain statements hold.
For example, that there exists some `n` such that `n + n = 12`, which is called half a dozen:
```
open import 01-intro-nat using (Nat; _+_)
open import 02-dependent-types using (Σ; _,_)

half-a-dozen : Σ Nat (λ n → IsTrue ((n + n) =ℕ 12))
half-a-dozen = 6 , is-true
```

## The identity type
Touched upon earlier, the identity type is constructed as
```
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
infix 4 _≡_
```

Thusly,
```
one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-isnt-one : 1 ≡ 0 → ⊥
zero-isnt-one ()
```
which is what everyone wanted to know!


