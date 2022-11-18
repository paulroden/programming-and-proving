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
classicalBottom : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
classicalBottom = λ x₁ → x₁ (right (λ x₀ → x₁ (left x₀)))
-- #TODO: revisit -- how does this work; should it involve some ¬ (¬ x)?
```


