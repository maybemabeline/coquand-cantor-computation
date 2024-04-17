```agda
open import term-syntax

extend-renaming : {Γ Δ : Ctx}
  → ({A : Type} → A c∈ Γ → A c∈ Δ)
    --------------------------------------
  → {A B : Type} → A c∈ (Γ , B) → A c∈ (Δ , B)
extend-renaming ρ here = here
extend-renaming ρ (there x) = there (ρ x)
rename : {Γ Δ : Ctx}
  → ({A : Type} → A c∈ Γ → A c∈ Δ)
    -------------------------
  → {A : Type} → Γ ⊢ A → Δ ⊢ A
rename ρ (var x) = var (ρ x)
rename ρ (lam t) = lam (rename (extend-renaming ρ) t)
rename ρ (app t u) = app (rename ρ t) (rename ρ u)
rename ρ zero = zero
rename ρ (succ t) = succ (rename ρ t)
rename ρ (natrec t0 tS) = natrec (rename ρ t0) (rename ρ tS)
rename ρ false = false
rename ρ true = true
rename ρ (boolrec t0 t1) = boolrec (rename ρ t0) (rename ρ t1)
rename ρ generic = generic
extend-subst : {Γ Δ : Ctx} →
  ({A : Type} → A c∈ Γ → Δ ⊢ A) →
  ---------------------------------------
  {A B : Type} → A c∈ (Γ , B) → (Δ , B) ⊢ A
extend-subst σ here = var here
extend-subst σ (there x) = rename there (σ x)
subst : {Γ Δ : Ctx} →
 ({A : Type} → A c∈ Γ → Δ ⊢ A) →
 -------------------------
 {A : Type} → Γ ⊢ A → Δ ⊢ A
subst σ (var x) = σ x
subst σ (lam t) = lam (subst (extend-subst σ) t)
subst σ (app t u) = app (subst σ t) (subst σ u)
subst σ zero = zero
subst σ (succ t) = succ (subst σ t)
subst σ (natrec t0 tS) = natrec (subst σ t0) (subst σ tS)
subst σ false = false
subst σ true = true
subst σ (boolrec t0 t1) = boolrec (subst σ t0) (subst σ t1)
subst σ generic = generic
_[_] : {Γ : Ctx} {A B : Type}
  → (Γ , B) ⊢ A
  → Γ ⊢ B
    -----
  → Γ ⊢ A
_[_] {Γ} {B = B} t u = subst σ t where
  σ : {A : Type} → A c∈ (Γ , B) → Γ ⊢ A
  σ here = u
  σ (there x) = var x
```
