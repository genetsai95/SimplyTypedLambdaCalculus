module STLC.Conversion where

open import Prelude
open import STLC.Base
open import STLC.Renaming
open import STLC.Substitution
open import STLC.Lemmas

data _⟶_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    same : {t t' : Γ ⊢ σ} → t ≡ t' → t ⟶ t'
    β-ƛ : {t : σ ∷ Γ ⊢ τ}{s : Γ ⊢ σ} → (ƛ t) · s ⟶ t [ s /x]
    β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₁ (t , s) ⟶ t
    β-π₂ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₂ (t , s) ⟶ s
    ξ-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t ⟶ t' → s ⟶ s' → t · s ⟶ t' · s'
    ξ-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t ⟶ t' → s ⟶ s' → (t , s) ⟶ (t' , s')
    ξ-π₁ : {t t' : Γ ⊢ σ ẋ τ} → t ⟶ t' → π₁ t ⟶ π₁ t'
    ξ-π₂ : {t t' : Γ ⊢ σ ẋ τ} → t ⟶ t' → π₂ t ⟶ π₂ t'
    ξ-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t ⟶ t' → (ƛ t) ⟶ (ƛ t')
    η-ƛ : {t : Γ ⊢ σ ⇒ τ} → t ⟶ (ƛ (weaken {τ = σ} t · (` ze)))
    η-pair : {t : Γ ⊢ σ ẋ τ} → t ⟶ (π₁ t , π₂ t)

data _⟶⋆_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    base : {t : Γ ⊢ σ} → t ⟶⋆ t
    step : {t u v : Γ ⊢ σ} → t ⟶ u → u ⟶⋆ v → t ⟶⋆ v

infixr 22 _▷_
_▷_ : {t u v : Γ ⊢ σ} → t ⟶⋆ u → u ⟶⋆ v → t ⟶⋆ v
base ▷ rs = rs
(step x rs1) ▷ rs2 = step x (rs1 ▷ rs2)

map-π₁ : {t u : Γ ⊢ σ ẋ τ} → t ⟶⋆ u → π₁ t ⟶⋆ π₁ u
map-π₁ base = base
map-π₁ (step x rs) = step (ξ-π₁ x) (map-π₁ rs)

map-π₂ : {t u : Γ ⊢ σ ẋ τ} → t ⟶⋆ u → π₂ t ⟶⋆ π₂ u
map-π₂ base = base
map-π₂ (step x rs) = step (ξ-π₂ x) (map-π₂ rs)

map-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t ⟶⋆ t' → s ⟶⋆ s' → (t , s) ⟶⋆ (t' , s')
map-pair base base = base
map-pair base (step x rs) = step (ξ-pair (same refl) x) (map-pair base rs)
map-pair (step x rs) base = step (ξ-pair x (same refl)) (map-pair rs base)
map-pair (step x rs1) (step y rs2) = step (ξ-pair x y) (map-pair rs1 rs2)

map-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t ⟶⋆ t' → s ⟶⋆ s' → (t · s) ⟶⋆ (t' · s')
map-app base base = base
map-app base (step x rs) = step (ξ-app (same refl) x) (map-app base rs)
map-app (step x rs) base = step (ξ-app x (same refl)) (map-app rs base)  
map-app (step x rs1) (step y rs2) = step (ξ-app x y) (map-app rs1 rs2)

map-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t ⟶⋆ t' → (ƛ t) ⟶⋆ (ƛ t')
map-ƛ base = base
map-ƛ (step x rs) = step (ξ-ƛ x) (map-ƛ rs)

rename-ξ : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t ⟶ t' → rename ρ t ⟶ rename ρ t'
rename-ξ ρ (same refl) = same refl
rename-ξ ρ {(ƛ t) · s} {t'} β-ƛ = transport (λ y → ((ƛ rename (lift ρ) t) · rename ρ s) ⟶ y) (subst-rename≡rename-subst ρ t {s}) (β-ƛ {t = rename (lift ρ) t} {rename ρ s})
rename-ξ ρ β-π₁ = β-π₁
rename-ξ ρ β-π₂ = β-π₂
rename-ξ ρ (ξ-app r s) = ξ-app (rename-ξ ρ r) (rename-ξ ρ s)
rename-ξ ρ (ξ-pair r s) = ξ-pair (rename-ξ ρ r) (rename-ξ ρ s)
rename-ξ ρ (ξ-π₁ r) = ξ-π₁ (rename-ξ ρ r)
rename-ξ ρ (ξ-π₂ r) = ξ-π₂ (rename-ξ ρ r)
rename-ξ ρ (ξ-ƛ r) = ξ-ƛ (rename-ξ (lift ρ) r)
rename-ξ ρ {t} η-ƛ = transport (λ y → rename ρ t ⟶ (ƛ y · (` ze))) (≡-sym (rename-lift-weaken≡weaken-rename ρ t)) (η-ƛ {t = rename ρ t})
rename-ξ ρ η-pair = η-pair

map-rename : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t ⟶⋆ t' → rename ρ t ⟶⋆ rename ρ t'
map-rename ρ base = base
map-rename ρ (step r rs) = step (rename-ξ ρ r) (map-rename ρ rs)

subst-ξ : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t ⟶ t' → subst t ts ⟶ subst t' ts
subst-ξ ts (same refl) = same refl
subst-ξ ts {(ƛ t) · s} β-ƛ = transport (λ y → (subst ((ƛ t) · s) ts) ⟶ y) eq β-ƛ
    where
        eq : (subst t (ts ↑) [ subst s ts /x]) ≡ subst (t [ s /x]) ts
        eq = (subst t (ts ↑) [ subst s ts /x])
           ≡⟨ lem[sub1] t ts (subst s ts) ⟩ 
              subst t (subst s ts ∷ ts)
           ≡⟨ cong (λ y → subst t (subst s ts ∷ y)) (≡-sym (idSub⊙ ts)) ⟩ 
              subst t (subst s ts ∷ (idSub ⊙ ts))
           ≡⟨ refl ⟩ 
              subst t ((s ∷ idSub) ⊙ ts)
           ≡⟨ ≡-sym (subsub t {s ∷ idSub} {ts}) ⟩ 
              subst (subst t (s ∷ idSub)) ts
           ≡⟨ refl ⟩ 
              subst (t [ s /x]) ts
           ∎
subst-ξ ts β-π₁ = β-π₁
subst-ξ ts β-π₂ = β-π₂
subst-ξ ts (ξ-app r r') = ξ-app (subst-ξ ts r) (subst-ξ ts r')
subst-ξ ts (ξ-pair r r') = ξ-pair (subst-ξ ts r) (subst-ξ ts r')
subst-ξ ts (ξ-π₁ r) = ξ-π₁ (subst-ξ ts r)
subst-ξ ts (ξ-π₂ r) = ξ-π₂ (subst-ξ ts r)
subst-ξ ts (ξ-ƛ r) = ξ-ƛ (subst-ξ (ts ↑) r)
subst-ξ ts {t} η-ƛ = transport (λ y → subst t ts ⟶ (ƛ y · (` ze))) (≡-sym (subst-weaken-↑ t ts)) (η-ƛ {t = subst t ts})
subst-ξ ts η-pair = η-pair

map-subst : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t ⟶⋆ t' → subst t ts ⟶⋆ subst t' ts
map-subst ts base = base
map-subst ts (step r rs) = step (subst-ξ ts r) (map-subst ts rs)