# Chapter 4: Equational Reasoning in Agda

This chapter looks to Graham Hutton's book _Programming in Haskell_ to use equational reasoning to prove properties of programing. Agda excels at this.
To start with, we define some 'helper' operators which allow proof in Agda to follow a logical set of steps, similar to those with pen and paper.
```
open import 03-curry-howard using (_≡_; refl; trans)

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A}
       → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix  1 begin_
infix  3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_
```

Let's try proving that `reverse`ing a singleton list does no change the list:
```
open import 01-intro-nat using (List; []; _∷_; _++_)

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

-- given the above definitions, let the proving begin - with the singleton case for now
reverse-singleton : {A : Set} (x : A) → reverse [ x ] ≡ [ x ]
reverse-singleton x =
  begin
    reverse [ x ]
  =⟨⟩
    reverse (x ∷ [])
  =⟨⟩
    reverse [] ++ [ x ]
  =⟨⟩
    [] ++ [ x ]
  =⟨⟩
    [ x ]
  end
```

## Proof by cases and induction
Let's prove that, for all natural numbers `n`, `n + 0 = n` (noting that the definition of `_+_` defines `0 + n`, which has the operands flipped).
```
open import 01-intro-nat using (Nat; zero; succ; _+_)
open import 03-curry-howard using (cong)

add-n-zero : (n : Nat) → n + zero ≡ n
add-n-zero zero =     -- base (zero) case
  begin
    zero + zero       -- applying + (with `zero + m`;  m as zero)
  =⟨⟩
    zero
  end
add-n-zero (succ n) =
  begin
    (succ n) + zero   -- applying + (with `(succ n) + m`; m as zero)
  =⟨⟩
    succ (n + zero)
  =⟨ cong succ (add-n-zero n)  ⟩  -- by induction
   succ n
  end
```

### Exercise 4.1. Prove that `m + succ n = succ (m + n)` for all `n, m ∈ ℕ`.
```
add-succ-n : (m n : Nat) → m + (succ n) ≡ succ (m + n)
add-succ-n zero n =
  begin
    zero + succ n
  =⟨⟩  -- apply `zero + m = m`
    succ n
  =⟨⟩
    succ (zero + n)
  end
add-succ-n (succ m) n =
  begin
    succ m + succ n
  =⟨⟩
    succ (m + succ n)
  =⟨ cong succ (add-succ-n m n) ⟩
    succ (succ (m + n))
  end
```
<Continued>
Next, for use the previous lemma (`add-n-zero`) and the above one (`add-succ-n`) to prove commutativity of addition over ℕ, i.e. that ∀ m, n ∈ ℕ, `m + n = n + m`.
```
add-commute : (m n : Nat) → m + n ≡ n + m
add-commute m zero =
  begin  
    m + zero  -- case 1/2: `n` is zero
  =⟨ add-n-zero m ⟩
    m
  =⟨⟩
    zero + m  -- we've swapped the order ⇒ it commutes
  end
add-commute m (succ n) =
  begin
    m + (succ n)  -- case 2/2: `n` is (succ n)  (*)
  =⟨ (add-succ-n m n) ⟩
    succ (m + n)
  =⟨ cong succ (add-commute m n) ⟩  -- by induction
    succ (n + m) 
  =⟨⟩
    (succ n) + m  -- we've swapped the order from (*) ⇒ it commutes and is shown by induction
  end
```