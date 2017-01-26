open import Agda.Primitive using (_⊔_)

-- Set being type of all types (which is infinitely nested as Set₀ Set₁ etc
postulate 
  String : Set

{-# BUILTIN STRING String #-}

data bool : Set where
  tt : bool
  ff : bool

ex₀ : bool → String
ex₀ tt = "true"
ex₀ ff = "false"

-- parameterization over all "Sets" 
-- otherwise we are limited to types that ∈ Set
if_then_else_ : ∀ { ℓ } { A : Set ℓ } → bool → A → A → A
if tt then x else y = x
if ff then x else y = y

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_plus_ : ℕ → ℕ → ℕ
zero   plus n = n
succ m plus n = succ (m plus n)

ex₁ : ℕ
ex₁ = 5

data [_] (A : Set) : Set where
  ♢   : [ A ]
  _,_ : A → [ A ] → [ A ]

infixr 6 _,_

_++_ : ∀{ α } → [ α ] → [ α ] → [ α ]
♢ ++ ys        = ys
(x , xs) ++ ys = x , xs ++ ys 

ex₂ : [ ℕ ]
ex₂ = 5 , 6 , ♢

-- why is this equivalent to 
--data _≡_ { α : Set } (x : α) : α → Set where
--  refl : x ≡ x

-- syntactical identity
data _≡_ { ℓ } { α : Set ℓ} : α → α → Set ℓ where
  refl : ∀ { x : α } → x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

data ⊥ : Set where

ex₃ : (2 plus 3) ≡ 5
ex₃ = refl

-- logical negation in intutionistic logic
ex₄ : 0 ≡ 1 → ⊥
ex₄ ()

cong : ∀ { ℓ } { A B : Set ℓ } → { a b : A } { f : A → B } → a ≡ b → f a ≡ f b
cong refl = refl

ex₅ : ∀ { n } → (n plus 0) ≡ n
ex₅ {zero}    = refl
ex₅ {succ n1} = cong { f = succ } ex₅

-- rewrites and dot patterns ??

data _+_ (α : Set) (β : Set) : Set where
  left  : α → α + β
  right : β → α + β

ex₆ : String + ℕ
ex₆ = left "foo"

ex₇ : String + ℕ
ex₇ = right 5

record _∨_ (α β : Set) : Set where
  constructor _,_
  field
    fst : bool
    snd : if fst then β else α

tosum : ∀ { α β } → α + β → α ∨ β
tosum (left a)  = ff , a
tosum (right b) = tt  , b

unsum : ∀ { α β } → α ∨ β → α + β 
unsum (ff , a) = left a
unsum (tt , b) = right b

tosum∘unsum : ∀ { α β } → (p : α ∨ β) → (tosum (unsum p)) ≡ p
tosum∘unsum (tt , b) = refl
tosum∘unsum (ff , b) = refl

unsum∘tosum : ∀ { α β } → (p : α + β) → (unsum (tosum p)) ≡ p
unsum∘tosum (left a)  = refl
unsum∘tosum (right b) = refl

--- Thus α + β is same as dependently typed α ∨ β. Further generalizing

record Σ (I : Set) (V : I -> Set) : Set where
  constructor _,_
  field
    fst : I
    snd : V fst

--- now α ∨ β can be written as
-- this is on the types, not on values
or : Set → Set → Set
or x y = Σ bool (λ b → if b then x else y)

-- assume V does not depend on I, we get products
twice : Set → Set
twice x = Σ bool (λ b → x)


