module STLC.Reduction where

open import Prelude
open import STLC.Base
open import STLC.Renaming
open import STLC.Substitution
open import STLC.Lemmas


-- definition of β-reduction
data _→β_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    same : {t t' : Γ ⊢ σ} → t ≡ t' → t →β t'
    β-ƛ : {t : σ ∷ Γ ⊢ τ}{s : Γ ⊢ σ} → (ƛ t) · s →β t [ s /x]
    β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₁ (t , s) →β t
    β-π₂ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₂ (t , s) →β s
    ξ-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t →β t' → s →β s' → t · s →β t' · s'
    ξ-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t →β t' → s →β s' → (t , s) →β (t' , s')
    ξ-π₁ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₁ t →β π₁ t'
    ξ-π₂ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₂ t →β π₂ t'
    ξ-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t →β t' → (ƛ t) →β (ƛ t')

infixr 33 _‣_
data _→β*_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    ✦ : {t : Γ ⊢ σ} → t →β* t
    _‣_ : {t u v : Γ ⊢ σ} → t →β u → u →β* v → t →β* v

infixr 35 _▷_
_▷_ : {t u v : Γ ⊢ σ} → t →β* u → u →β* v → t →β* v
✦ ▷ rs = rs
(r ‣ rs₁) ▷ rs₂ = r ‣ rs₁ ▷ rs₂


-- ξ-rules for →β*

map-π₁ : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₁ t →β* π₁ u
map-π₁ ✦ = ✦
map-π₁ (r ‣ rs) = ξ-π₁ r ‣ map-π₁ rs

map-π₂ : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₂ t →β* π₂ u
map-π₂ ✦ = ✦
map-π₂ (r ‣ rs) = ξ-π₂ r ‣ map-π₂ rs

map-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t →β* t' → s →β* s' → (t , s) →β* (t' , s')
map-pair ✦ ✦ = ✦
map-pair ✦ (r ‣ rs) = ξ-pair (same refl) r ‣ map-pair ✦ rs
map-pair (r ‣ rs) ✦ = ξ-pair r (same refl) ‣ map-pair rs ✦
map-pair (r₁ ‣ rs₁) (r₂ ‣ rs₂) = ξ-pair r₁ r₂ ‣ map-pair rs₁ rs₂

map-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t →β* t' → s →β* s' → (t · s) →β* (t' · s')
map-app ✦ ✦ = ✦
map-app ✦ (r ‣ rs) = ξ-app (same refl) r ‣ map-app ✦ rs
map-app (r ‣ rs) ✦ = ξ-app r (same refl) ‣ map-app rs ✦  
map-app (r₁ ‣ rs₁) (r₂ ‣ rs₂) = ξ-app r₁ r₂ ‣ map-app rs₁ rs₂

map-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t →β* t' → (ƛ t) →β* (ƛ t')
map-ƛ ✦ = ✦
map-ƛ (r ‣ rs) = ξ-ƛ r ‣ map-ƛ rs

rename-ξ : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t →β t' → rename ρ t →β rename ρ t'
rename-ξ ρ (same refl) = same refl
rename-ξ ρ {(ƛ t) · s} {t'} β-ƛ = transport (λ y → ((ƛ rename (lift ρ) t) · rename ρ s) →β y) (subst-rename≡rename-subst ρ t {s}) (β-ƛ {t = rename (lift ρ) t} {rename ρ s})
rename-ξ ρ β-π₁ = β-π₁
rename-ξ ρ β-π₂ = β-π₂
rename-ξ ρ (ξ-app r s) = ξ-app (rename-ξ ρ r) (rename-ξ ρ s)
rename-ξ ρ (ξ-pair r s) = ξ-pair (rename-ξ ρ r) (rename-ξ ρ s)
rename-ξ ρ (ξ-π₁ r) = ξ-π₁ (rename-ξ ρ r)
rename-ξ ρ (ξ-π₂ r) = ξ-π₂ (rename-ξ ρ r)
rename-ξ ρ (ξ-ƛ r) = ξ-ƛ (rename-ξ (lift ρ) r)

map-rename : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t →β* t' → rename ρ t →β* rename ρ t'
map-rename ρ ✦ = ✦
map-rename ρ (r ‣ rs) = rename-ξ ρ r ‣ map-rename ρ rs

subst-ξ : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t →β t' → subst t ts →β subst t' ts
subst-ξ ts (same refl) = same refl
subst-ξ ts {(ƛ t) · s} β-ƛ = transport (λ y → (subst ((ƛ t) · s) ts) →β y) eq β-ƛ
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

map-subst : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t →β* t' → subst t ts →β* subst t' ts
map-subst ts ✦ = ✦
map-subst ts (r ‣ rs) = subst-ξ ts r ‣ map-subst ts rs


-- β-reduction of substitutions

data _⇛β_ : Sub Γ Δ → Sub Γ Δ → Set where
   [] : {ts ts' : Sub [] Δ} → ts ⇛β ts'
   _∷_ : {t t' : Δ ⊢ σ}{ts ts' : Sub Γ Δ} → t →β t' → ts ⇛β ts' → (t ∷ ts) ⇛β (t' ∷ ts')

lookup⇛β : {ts ts' : Sub Γ Δ}{σ : Type}(x : Γ ∋ σ) → ts ⇛β ts' → lookup x ts →β lookup x ts'
lookup⇛β ze (r ∷ rs) = r
lookup⇛β (su x) (r ∷ rs) = lookup⇛β x rs

mapSub⇛β : {f : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ} → (∀{σ} → {t t' : Δ ⊢ σ} → t →β t' → f t →β f t') → {ts ts' : Sub Γ Δ} → ts ⇛β ts' → mapSub f ts ⇛β mapSub f ts'
mapSub⇛β psv [] = []
mapSub⇛β psv (r ∷ rs) = psv r ∷ mapSub⇛β psv rs

_⤊β : ∀{σ} → {ts ts' : Sub Γ Δ} → ts ⇛β ts' → (_↑ {σ = σ} ts) ⇛β (ts' ↑)
rs ⤊β = same refl ∷ mapSub⇛β (rename-ξ wk) rs

idSub⇛βidSub : ∀{Γ} → idSub {Γ} ⇛β idSub
idSub⇛βidSub {[]} = []
idSub⇛βidSub {σ ∷ Γ} = idSub⇛βidSub ⤊β

subst-Sub-ξ : (t : Γ ⊢ σ){ts ts' : Sub Γ Δ} → ts ⇛β ts' → subst t ts →β subst t ts'
subst-Sub-ξ (` ze) (r ∷ rs) = r
subst-Sub-ξ (` su x) (r ∷ rs) = subst-Sub-ξ (` x) rs
subst-Sub-ξ yes rs = same refl
subst-Sub-ξ no rs = same refl
subst-Sub-ξ ⟨⟩ rs = same refl
subst-Sub-ξ (t , s) rs = ξ-pair (subst-Sub-ξ t rs) (subst-Sub-ξ s rs)
subst-Sub-ξ (π₁ t) rs = ξ-π₁ (subst-Sub-ξ t rs)
subst-Sub-ξ (π₂ t) rs = ξ-π₂ (subst-Sub-ξ t rs)
subst-Sub-ξ (t · s) rs = ξ-app (subst-Sub-ξ t rs) (subst-Sub-ξ s rs)
subst-Sub-ξ (ƛ t) rs = ξ-ƛ (subst-Sub-ξ t (rs ⤊β)) 

/x-ξ : (t : σ ∷ Γ ⊢ τ){s s' : Γ ⊢ σ} → s →β s' → (t [ s /x]) →β (t [ s' /x])
/x-ξ t r = subst-Sub-ξ t (r ∷ idSub⇛βidSub)

map-/x : (t : σ ∷ Γ ⊢ τ){s s' : Γ ⊢ σ} → s →β* s' → (t [ s /x]) →β* (t [ s' /x])
map-/x t ✦ = ✦
map-/x t (r ‣ rs) = /x-ξ t r ‣ map-/x t rs