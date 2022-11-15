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
