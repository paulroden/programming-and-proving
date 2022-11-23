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
Now for something more insightful: proving that `reverse`ing a list twice yields the same list.
Towards this, we'll need to provide auxilliary lemmas, proving that  distributes over list concatenation (i.e. reversing a list comprised of two others is the same as reversing the two lists and 'flip' concatenating them), i.e.
`
  reverse (xs ++ ys) = reverse ys ++ reverse xs
`

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
  =⟨ cong (x ∷_) (reverse-reverse xs) ⟩  -- NOTE: (x ::_) is curried _∷_ with the first argument applied, a.k.a 'section syntax`: `λ xs → x ∷ xs`
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
    reverse-distributivity (x ∷ xs) ys =
      begin
        reverse ((x ∷ xs) ++ ys)
      =⟨⟩
        reverse (x ∷ (xs ++ ys))
      =⟨⟩
        reverse (xs ++ ys) ++ reverse [ x ]
      =⟨⟩
        reverse (xs ++ ys) ++ [ x ]
      =⟨ cong (_++ [ x ]) (reverse-distributivity xs ys) ⟩
        (reverse ys ++ reverse xs) ++ [ x ]
      =⟨ append-assoc (reverse ys) (reverse xs) [ x ] ⟩
        reverse ys ++ (reverse xs ++ [ x ]) 
      =⟨⟩
        reverse ys ++ reverse (x ∷ xs)
      end
      where
        append-assoc : {A : Set} → (xs ys zs : List A)
                     → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
        append-assoc [] ys zs =
          begin
            ([] ++ ys) ++ zs
          =⟨⟩
            ys ++ zs
          =⟨⟩
            [] ++ (ys ++ zs)
          end
        append-assoc (x ∷ xs) ys zs =
          begin
            ((x ∷ xs) ++ ys) ++ zs
          =⟨⟩
            (x ∷ (xs ++ ys)) ++ zs
          =⟨⟩
            x ∷ ((xs ++ ys) ++ zs)
          =⟨ cong (x ∷_) (append-assoc xs ys zs) ⟩
            x ∷ (xs ++ (ys ++ zs))
          =⟨⟩
            (x ∷ xs) ++ (ys ++ zs)
          end
```
### Exercise 4.3. Proofs of `append-[]` and `append-assoc` above.


## Proving the functor laws for `map`.
The functor laws, for some functor `f`, comprise:
  Identity: `f id = id`
  Composition: `f (g ∘ h) = f g ∘ f g`

Let us prove these for `f` as `map` on `List`s.
```
open import 01-intro-nat using (id; map)

-- Identity Law
map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id [] =
  begin
    map id []
  =⟨⟩
    []
  end
map-id (x ∷ xs) =
  begin
    map id (x ∷ xs)
  =⟨⟩
    id x ∷ map id xs
  =⟨⟩
    x ∷ map id xs
  =⟨ cong (x ∷_) (map-id xs) ⟩  -- by induction; using 'section syntax'
    x ∷ xs
  end

-- Composition Law
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ h = λ x → g (h x)

map-compose : {A B C : Set} → (f : B → C) (g : A → B) (xs : List A)
            → map (f ∘ g) xs ≡ map f (map g xs)
map-compose f g [] =
  begin
    map (f ∘ g) []
  =⟨⟩
    []
  =⟨⟩
    map f []
  =⟨⟩
    map f (map g [])
  end
map-compose f g (x ∷ xs) =
  begin
    map (f ∘ g) (x ∷ xs)
  =⟨⟩
    (f ∘ g) x ∷ map (f ∘ g) xs
  =⟨⟩
    f (g x) ∷ map (f ∘ g) xs
  =⟨ cong (f (g x) ∷_) (map-compose f g xs) ⟩
    f (g x) ∷ map f (map g xs)
  =⟨⟩
    map f (g x ∷ map g xs)
  =⟨⟩
    map f (map g (x ∷ xs))
  end
```

### Exercise 4.4. Prove that `length (map f xs) is equal to `length xs` for all `xs`.
```
map-length : {A B : Set} → (f : A → B) (xs : List A)
           → length (map f xs) ≡ length xs
map-length {A} f [] =
  begin
    length (map f [])
  =⟨⟩
    length {A} []
  end
map-length f (x ∷ xs) =
   begin
     length (map f (x ∷ xs))
   =⟨⟩
     length (f x ∷ (map f xs))
   =⟨⟩
     succ (length (map f xs))
   =⟨ cong succ (map-length f xs) ⟩
    succ (length xs)
   =⟨⟩
     length (x ∷ xs)
   end
```

### Exercise 4.5 Define the functions `take` and `drop` that respectively return or re- move the first `n` elements of the list (or all elements if the list is shorter). Prove that for any number n and any list xs, we have `take n xs ++ drop n xs = xs`.
```
take : {A : Set} → Nat → List A → List A
take zero     _        = []
{-# CATCHALL #-}
take _        []       = []
take (succ n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero     xs       = xs
drop (succ n) []       = []
drop (succ n) (x ∷ xs) = drop n xs

take-drop : {A : Set} (n : Nat) (xs : List A)
         → take n xs ++ drop n xs ≡ xs
take-drop zero [] =
  begin
    take zero [] ++ drop zero []
  =⟨⟩
    [] ++ []
  =⟨⟩
    []
  end
take-drop zero xs =
  begin
    take zero xs ++ drop zero xs
  =⟨⟩
    [] ++ xs
  =⟨⟩
    xs
  end
take-drop (succ n) [] =
  begin
    take (succ n) [] ++ drop (succ n) []
  =⟨⟩
    [] ++ []
  =⟨⟩
    []
  end
take-drop (succ n) (x ∷ xs) =
  begin
    take (succ n) (x ∷ xs) ++ drop (succ n) (x ∷ xs)
  =⟨⟩
    (x ∷ (take n xs)) ++ (drop n xs)
  =⟨ cong (x ∷_) (take-drop n xs) ⟩
    x ∷ xs
  end
```
