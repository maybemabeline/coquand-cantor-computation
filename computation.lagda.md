```agda
open import condition-lists
open import naturals
open import term-syntax
open import substitution
open Cond

data computation : {A : Type} {Γ : Ctx} ->
  (p : Cond nat) -> (Γ ⊢ A) -> {I : Part p} -> formal-sum A Γ I -> Set
  where

  step-app :
    {A B : Type} {Γ : Ctx} {p : Cond nat} {t : Γ ⊢ (A => B)} {u : Γ ⊢ A}
    {I : Part p} {Σ : formal-sum (A => B) Γ I} ->
      computation p t Σ ->
      computation p (app t u) (bind Σ (λ ti → app ti u))

  app-lam :
    {A B : Type} {Γ : Ctx} {p : Cond nat} {t : (Γ , A) ⊢ B} {u : Γ ⊢ A} ->
    computation p (app (lam t) u) (triv-sum p (t [ u ]))

  boolrec-false : {B : Type} {Γ : Ctx} {p : Cond nat} {t0 t1 : Γ ⊢ B} ->
    computation p (app (boolrec t0 t1) false) (triv-sum p t0)

  boolrec-true : {B : Type} {Γ : Ctx} {p : Cond nat} {t0 t1 : Γ ⊢ B} ->
    computation p (app (boolrec t0 t1) true) (triv-sum p t1)

  boolrec-step : {B : Type} {Γ : Ctx} {p : Cond nat} {t0 t1 : Γ ⊢ B} {t : Γ ⊢ N2}
    {I : Part p} {Σ : formal-sum N2 Γ I} ->
      computation p t Σ ->
      computation p (app (boolrec t0 t1) t) (bind Σ (app (boolrec t0 t1)))

  natrec-zero : {B : Type} {Γ : Ctx} {p : Cond nat} {t0 : Γ ⊢ B}
    {tS : Γ ⊢ (N => (B => B))} ->
    computation p (app (natrec t0 tS) zero) (triv-sum p t0)

  natrec-succ : {B : Type} {Γ : Ctx} {p : Cond nat} {t0 : Γ ⊢ B} {t : Γ ⊢ N}
    {tS : Γ ⊢ (N => (B => B))} ->
    computation p
      (app (natrec t0 tS) (succ t))
      (triv-sum p (app (app tS t) (app (natrec t0 tS) t)))

  natrec-step : {B : Type} {Γ : Ctx} {p : Cond nat} {t0 : Γ ⊢ B} {t : Γ ⊢ N}
    {tS : Γ ⊢ (N => (B => B))} ->
    {I : Part p} {Σ : formal-sum N Γ I} ->
      computation p t Σ ->
      computation p (app (natrec t0 tS) t) (bind Σ (app (natrec t0 tS)))

  app-generic-triv : {Γ : Ctx} {p : Cond nat} {n : nat} {n∈p : n ∈ list-Cond p} ->
    computation {Γ = Γ} p
      (app generic (canon-nat n))
      (triv-sum p (canon-bool (cond-lookup n n∈p (is-cond-Cond p))))

  app-generic-split : {Γ : Ctx} {p : Cond nat} {n : nat} {n∉p : ¬ (n ∈ list-Cond p)} ->
    computation {Γ = Γ} p
      (app generic (canon-nat n))
      (glue-sum p
        (triv-sum (Cond-cons n false p n∉p) false)
        (triv-sum (Cond-cons n true p n∉p) true))

  app-generic-step : {Γ : Ctx} {p : Cond nat} {t : Γ ⊢ N} {I : Part p}
    {Σ : formal-sum N Γ I} ->
    computation p t Σ ->
    computation p (app generic t) (bind Σ (app generic))


data is-value : {A : Type} {Γ : Ctx} {p : Cond nat} {I : Part p} ->
  formal-sum A Γ I -> Set where

  value-bool : {Γ : Ctx} {p : Cond nat} {I : Part p} (b : bool) ->
    is-value {Γ = Γ } (triv-sum p (canon-bool b))

  value-nat : {Γ : Ctx} {p : Cond nat} {I : Part p} (n : nat) ->
    is-value {Γ = Γ } (triv-sum p (canon-nat n ))

  value-sum : {A : Type} {Γ : Ctx} {p : Cond nat} {n : nat} {n∉l : ¬ (n ∈ list-Cond p)}
    {I : Part (Cond-cons n false p n∉l)} {ΣI : formal-sum A Γ I}
    {J : Part (Cond-cons n true p n∉l)} {ΣJ : formal-sum A Γ J} ->
    is-value ΣI -> is-value ΣJ -> is-value (glue-sum p ΣI ΣJ)
```
