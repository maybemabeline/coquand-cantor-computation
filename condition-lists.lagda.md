```agda
data empty : Set where

¬ : (A : Set) -> Set
¬ A = A -> empty

data bool : Set where
  true : bool
  false : bool

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

is-decidable : (A : Set) -> Set
is-decidable A = A + ¬ A

data Id {A : Set} : A -> A -> Set where
  refl : {a : A} -> Id a a

mutual
  data List (A : Set) : Set where
    nil :  List A
    cons : A -> List A -> List A

  data _∈_ {A : Set} : A -> List A -> Set where
    here : (a : A) -> (l : List A) -> a ∈ cons a l
    there : (a : A) -> (l : List A) -> (a ∈ l) -> (x : A) -> a ∈ (cons x l)

decidable-Id : (A : Set) -> Set
decidable-Id A = (x y : A) -> is-decidable (Id x y)

decidable-inhabitance : (A : Set) -> Set
decidable-inhabitance A = (a : A) -> (l : List A) -> is-decidable (a ∈ l)

decidable-inhabitance-of-decidable-Id : {A : Set} ->
 decidable-Id A -> decidable-inhabitance A
decidable-inhabitance-of-decidable-Id p a nil = inr λ ()
decidable-inhabitance-of-decidable-Id decId a (cons x l) with decId a x
... | inl refl = inl (here a l)
... | inr p with decidable-inhabitance-of-decidable-Id decId a l
... | inl α = inl (there a l α x)
... | inr q = inr (λ { (here .a .l) → p refl ; (there .a .l β .x) → q β})

data is-cond {A : Set} : List A -> Set where
  safe-nil : is-cond nil
  safe-cons : (a : A) -> (b : bool) -> (l : List A) -> ¬ (a ∈ l) ->
    is-cond l -> is-cond (cons a l)

record Cond (A : Set) : Set where
  field
    list-Cond : List A
    is-cond-Cond : is-cond list-Cond
open Cond

Cond-cons : {A : Set} -> (a : A) -> (b : bool) ->
  (p : Cond A) -> ¬ (a ∈ list-Cond p) -> Cond A
Cond-cons a b p α = record { list-Cond = cons a (list-Cond p)
                           ; is-cond-Cond = safe-cons a b (list-Cond p) α (is-cond-Cond p)
                           }

cond-lookup : {A : Set} -> {l : List A} -> (a : A) -> (a ∈ l) -> is-cond l -> bool
cond-lookup a (here a l) (safe-cons .a b .l α p) = b
cond-lookup a (there a l α x) (safe-cons .x _ .l _ p) = cond-lookup a α p

cond-matching : {A : Set} -> {l r : List A} -> is-cond l -> is-cond r -> Set
cond-matching {A} {l} {r} p q =
  (a : A) -> (α : a ∈ l) -> (β : a ∈ r) ->
  Id (cond-lookup a α p) (cond-lookup a β q)

list-union : {A : Set} -> decidable-inhabitance A -> (l r : List A) -> List A
list-union dec∈ l nil = l
list-union dec∈ l (cons x r) with dec∈ x l
... | inl α = list-union dec∈ l r
... | inr β = cons x (list-union dec∈ l r)

list-union-non-inhabited : {A : Set} -> (dec∈ : decidable-inhabitance A) -> (l r : List A) ->
  (a : A) -> ¬ (a ∈ l) -> ¬ (a ∈ r) -> ¬ (a ∈ list-union dec∈ l r)
list-union-non-inhabited dec∈ l nil a α β = α
list-union-non-inhabited dec∈ l (cons x r) a α β with dec∈ x l
... | inl γ = λ δ → list-union-non-inhabited dec∈ l r a α (λ ϵ → β (there a r ϵ x)) δ
... | inr γ =
  λ { (here _ _) → β (here a r)
    ; (there _ _ δ _) → list-union-non-inhabited dec∈ l r a α (λ ϵ → β (there a r ϵ x)) δ}

cond-union : {A : Set} -> (dec∈ : decidable-inhabitance A) -> {l r : List A} ->
  (p : is-cond l) -> (q : is-cond r) -> cond-matching p q -> is-cond (list-union dec∈ l r)
cond-union dec∈ p safe-nil m = p
cond-union {A} dec∈ {l = l} p (safe-cons a b r γ q) m with dec∈ a l
... | inl _ = cond-union dec∈ p q (λ x α β → m x α (there x r β a))
... | inr δ =
  safe-cons a b
    (list-union dec∈ l r)
    (list-union-non-inhabited dec∈ l r a δ γ)
    (cond-union dec∈ p q (λ x α β → m x α (there x r β a)))

```
