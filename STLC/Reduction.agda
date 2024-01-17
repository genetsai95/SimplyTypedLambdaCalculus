module STLC.Reduction where

open import Prelude
open import STLC.Base
open import STLC.Substitution

data _→β_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    β-refl : {t t' : Γ ⊢ σ} → t ≡ t' → t →β t'
    β-ƛ : {t : σ ∷ Γ ⊢ τ}{s : Γ ⊢ σ} → (ƛ t) · s →β t [ s /x]
    β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₁ (t , s) →β t
    β-π₂ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₂ (t , s) →β s
    ξ-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t →β t' → s →β s' → t · s →β t' · s'
    ξ-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t →β t' → s →β s' → (t , s) →β (t' , s')
    ξ-π₁ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₁ t →β π₁ t'
    ξ-π₂ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₂ t →β π₂ t'

data _→β*_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    β-base : {t : Γ ⊢ σ} → t →β* t
    β-step : {t u v : Γ ⊢ σ} → t →β u → u →β* v → t →β* v

-- data [_]β {Γ : Cxt}(P : (σ : Type) → Γ ⊢ σ → Set) : (τ : Type)(t : Γ ⊢ τ) → Set where
--     β-inj : {σ : Type}{t : Γ ⊢ σ} → P σ t → [ P ]β σ t
--     β-from : {σ : Type}(t' : Γ ⊢ σ){t : Γ ⊢ σ} → t' →β* t → [ P ]β σ t' → [ P ]β σ t 
--     β-to : {σ : Type}{t : Γ ⊢ σ}(t' : Γ ⊢ σ) → t →β* t' → [ P ]β σ t' → [ P ]β σ t
--     ξ-pair : {σ τ : Type}{t : Γ ⊢ σ}{s : Γ ⊢ τ} → [ P ]β σ t → [ P ]β τ s → [ P ]β (σ ẋ τ) (t , s)
--     β-abs : {σ τ : Type}{t : Γ ⊢ σ ⇒ τ} → ((s : Γ ⊢ σ) → P σ s → [ P ]β τ (t · s)) → [ P ]β (σ ⇒ τ) t

concatβ* : {t u v : Γ ⊢ σ} → t →β* u → u →β* v → t →β* v
concatβ* β-base rs = rs
concatβ* (β-step x rs1) rs2 = β-step x (concatβ* rs1 rs2)

map-π₁ : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₁ t →β* π₁ u
map-π₁ β-base = β-base
map-π₁ (β-step x rs) = β-step (ξ-π₁ x) (map-π₁ rs)

map-π₂ : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₂ t →β* π₂ u
map-π₂ β-base = β-base
map-π₂ (β-step x rs) = β-step (ξ-π₂ x) (map-π₂ rs)

map-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t →β* t' → s →β* s' → (t , s) →β* (t' , s')
map-pair β-base β-base = β-base
map-pair β-base (β-step x rs) = β-step (ξ-pair (β-refl refl) x) (map-pair β-base rs)
map-pair (β-step x rs) β-base = β-step (ξ-pair x (β-refl refl)) (map-pair rs β-base)
map-pair (β-step x rs1) (β-step y rs2) = β-step (ξ-pair x y) (map-pair rs1 rs2)

map-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t →β* t' → s →β* s' → (t · s) →β* (t' · s')
map-app β-base β-base = β-base
map-app β-base (β-step x rs) = β-step (ξ-app (β-refl refl) x) (map-app β-base rs)
map-app (β-step x rs) β-base = β-step (ξ-app x (β-refl refl)) (map-app rs β-base)  
map-app (β-step x rs1) (β-step y rs2) = β-step (ξ-app x y) (map-app rs1 rs2)