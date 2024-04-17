```agda
open import condition-lists
open import naturals
open Cond

data Type : Set where
  N : Type
  N2 : Type
  _=>_ : Type -> Type -> Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx -> Type -> Ctx

data _c∈_ : Type -> Ctx -> Set where
  here : {A : Type} {Γ : Ctx} -> A c∈ (Γ , A)
  there : {A B : Type} {Γ : Ctx} -> (A c∈ Γ) -> A c∈ (Γ , B)

data _⊢_ : Ctx -> Type -> Set where

  var : {A : Type} {Γ : Ctx} -> (A c∈ Γ) -> (Γ ⊢ A)

  lam : {A B : Type} {Γ : Ctx} -> ((Γ , A) ⊢ B) -> (Γ ⊢ (A => B))

  app : {A B : Type} {Γ : Ctx} -> (Γ ⊢ (A => B)) -> (Γ ⊢ A) -> (Γ ⊢ B)

  zero : {Γ : Ctx} -> (Γ ⊢ N)

  succ : {Γ : Ctx} -> (Γ ⊢ N) -> (Γ ⊢ N)

  natrec : {B : Type} {Γ : Ctx} -> (Γ ⊢ B) -> (Γ ⊢ (N => (B => B))) -> (Γ ⊢ (N => B))

  false : {Γ : Ctx} -> (Γ ⊢ N2)

  true : {Γ : Ctx} -> (Γ ⊢ N2)

  boolrec : {B : Type} {Γ : Ctx} -> (Γ ⊢ B) -> (Γ ⊢ B) -> (Γ ⊢ (N2 => B))

  generic : {Γ : Ctx} -> (Γ ⊢ (N => N2))

canon-nat : {Γ : Ctx} -> (n : nat) -> (Γ ⊢ N)
canon-nat zero = zero
canon-nat (succ n) = succ (canon-nat n)

canon-bool : {Γ : Ctx} -> (b : bool) -> (Γ ⊢ N2)
canon-bool true = true
canon-bool false = false

data Part : (p : Cond nat) -> Set where
  triv : (p : Cond nat) -> Part p
  glue : (p : Cond nat) -> (n : nat) -> (n∉l : ¬ (n ∈ list-Cond p)) ->
    Part (Cond-cons n false p n∉l) ->
    Part (Cond-cons n true p n∉l) ->
    Part p

data formal-sum (A : Type) (Γ : Ctx) : {p : Cond nat} -> Part p -> Set where
  triv-sum :  (p : Cond nat) -> (Γ ⊢ A) -> formal-sum A Γ (triv p)
  glue-sum : (p : Cond nat) -> {n : nat} -> {n∉l : ¬ (n ∈ list-Cond p)} ->
    {I : Part (Cond-cons n false p n∉l)} -> formal-sum A Γ I ->
    {J : Part (Cond-cons n true p n∉l)} -> formal-sum A Γ J ->
    formal-sum A Γ (glue p n n∉l I J)

bind : {p : Cond nat} {I : Part p} {A B : Type} {Γ : Ctx} ->
  formal-sum A Γ I -> ((Γ ⊢ A) -> (Γ ⊢ B)) -> formal-sum B Γ I
bind (triv-sum p t) f = triv-sum p (f t)
bind (glue-sum p Σ1 Σ2) f = glue-sum p (bind Σ1 f) (bind Σ2 f)
```
