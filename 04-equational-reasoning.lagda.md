# Chapter 4: Equational Reasoning in Agda

This chapter looks to Graham Hutton's book _Programming in Haskell_ to use equational reasoning to prove properties of programing. Agda excels at this.
To start with, we define some 'helper' operators which allow proof in Agda to follow a logical set of steps, similar to those with pen and paper.
```
open import 03-curry-howard using (_≡_; refl; sym; trans)

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

Continuing on from commutativity, let's prove that addition over ℕ is associative, i.e. `l + (m + n) = (l + m) + n`:
```
add-assoc : (l m n : Nat) → l + (m + n) ≡ (l + m) + n
add-assoc zero m n =
  begin
     zero + (m + n)
   =⟨⟩
     m + n
   =⟨⟩
     (zero + m) + n
  end 
add-assoc (succ l) m n =
  begin
    (succ l) + (m + n)
  =⟨⟩
    succ (l + (m + n))
  =⟨ cong succ (add-assoc l m n) ⟩
    succ ((l + m) + n)
  =⟨⟩
    (succ (l + m)) + n
  =⟨⟩
    (succ l + m) + n
  end
```

### Exercise 4.2. Consider the following function:
```
replicate : {A : Set} → Nat → A → List A
replicate zero     _ = []
replicate (succ n) x = x ∷ replicate n x
```
Prove that the length of `replicate n x` is always equal to n, by induction on the number n.
```
open import 01-intro-nat using (length)

replicate-is-length-n : {A : Set} → (n : Nat) → (x : A)
                      → length (replicate n x) ≡ n
replicate-is-length-n {A} zero x =
  begin
    length (replicate zero x)
  =⟨⟩
    length {A} []   -- note a type needs to be provided here, otherwise the type is ambiguous
  =⟨⟩
    zero
  end
replicate-is-length-n (succ n) x =
  begin
    length (replicate (succ n) x)
   =⟨⟩
    length (x ∷ replicate n x)
   =⟨⟩
    succ (length (replicate n x))
   =⟨ cong succ (replicate-is-length-n n x) ⟩
    succ n
  end
```

## Induction on lists
Now for something more insightful: proving that `reverse` distributes over list concatenation (i.e. reversing a list comprised of two others is the same as reversing the two lists and 'flip' concatenating them), i.e.
`
  reverse (xs ++ ys) = reverse ys ++ reverse xs
`

First, we'll need to prove that reversing a reversed list yields the original list.
```
reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] =
  begin
    reverse (reverse [])
  =⟨⟩
    reverse []
  =⟨⟩
    []
   end
reverse-reverse (x ∷ xs) = 
  begin
    reverse (reverse (x ∷ xs))
  =⟨⟩
    reverse (reverse xs ++ [ x ])
  =⟨ reverse-distributivity (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  =⟨⟩
   [ x ] ++ reverse (reverse xs)
  =⟨ cong (x ∷_) (reverse-reverse xs) ⟩  -- NOTE: (x ::_) is curried _∷_ with the first argument applied
    (x ∷ xs)
  end
  where
    reverse-distributivity : {A : Set} → (xs ys : List A)
                           → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
    reverse-distributivity [] ys =
      begin
        reverse ([] ++ ys)
      =⟨⟩
        reverse ys
      =⟨ sym (append-[] (reverse ys)) ⟩
        reverse ys ++ []
      =⟨⟩
        reverse ys ++ reverse []
      end
      where
        append-[] : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
        append-[] [] =
          begin
            [] ++ []
          =⟨⟩
            []
          end
        append-[] (x ∷ xs) =
          begin
            (x ∷ xs) ++ []
          =⟨⟩
            x ∷ (xs ++ [])
          =⟨ cong (x ∷_) (append-[] xs) ⟩ 
            x ∷ xs
          end
    reverse-distributivity (x ∷ xs) ys = {!!}
```
