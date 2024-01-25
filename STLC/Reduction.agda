module STLC.Reduction where

open import Prelude
open import STLC.Base
open import STLC.Renaming
open import STLC.Substitution
open import STLC.Lemmas

data _→β_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    β-refl : {t t' : Γ ⊢ σ} → t ≡ t' → t →β t'
    β-ƛ : {t : σ ∷ Γ ⊢ τ}{s : Γ ⊢ σ} → (ƛ t) · s →β t [ s /x]
    β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₁ (t , s) →β t
    β-π₂ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₂ (t , s) →β s
    ξ-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t →β t' → s →β s' → t · s →β t' · s'
    ξ-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t →β t' → s →β s' → (t , s) →β (t' , s')
    ξ-π₁ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₁ t →β π₁ t'
    ξ-π₂ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₂ t →β π₂ t'
    ξ-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t →β t' → (ƛ t) →β (ƛ t')

data _→β*_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    β-base : {t : Γ ⊢ σ} → t →β* t
    β-step : {t u v : Γ ⊢ σ} → t →β u → u →β* v → t →β* v

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

map-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t →β* t' → (ƛ t) →β* (ƛ t')
map-ƛ β-base = β-base
map-ƛ (β-step x rs) = β-step (ξ-ƛ x) (map-ƛ rs)

rename-ξ : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t →β t' → rename ρ t →β rename ρ t'
rename-ξ ρ (β-refl refl) = β-refl refl
rename-ξ ρ {(ƛ t) · s} {t'} β-ƛ = transport (λ y → ((ƛ rename (lift ρ) t) · rename ρ s) →β y) (subst-rename≡rename-subst ρ t {s}) (β-ƛ {t = rename (lift ρ) t} {rename ρ s})
rename-ξ ρ β-π₁ = β-π₁
rename-ξ ρ β-π₂ = β-π₂
rename-ξ ρ (ξ-app r s) = ξ-app (rename-ξ ρ r) (rename-ξ ρ s)
rename-ξ ρ (ξ-pair r s) = ξ-pair (rename-ξ ρ r) (rename-ξ ρ s)
rename-ξ ρ (ξ-π₁ r) = ξ-π₁ (rename-ξ ρ r)
rename-ξ ρ (ξ-π₂ r) = ξ-π₂ (rename-ξ ρ r)
rename-ξ ρ (ξ-ƛ r) = ξ-ƛ (rename-ξ (lift ρ) r)

map-rename : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t →β* t' → rename ρ t →β* rename ρ t'
map-rename ρ β-base = β-base
map-rename ρ (β-step r rs) = β-step (rename-ξ ρ r) (map-rename ρ rs)
