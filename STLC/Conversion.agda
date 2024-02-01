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

infixr 33 _‣_
data _⟶⋆_ : Γ ⊢ σ → Γ ⊢ σ → Set where
   ✦ : {t : Γ ⊢ σ} → t ⟶⋆ t
   _‣_ : {t u v : Γ ⊢ σ} → t ⟶ u → u ⟶⋆ v → t ⟶⋆ v

infixr 35 _▷_
_▷_ : {t u v : Γ ⊢ σ} → t ⟶⋆ u → u ⟶⋆ v → t ⟶⋆ v
✦ ▷ rs = rs
(r ‣ rs1) ▷ rs2 = r ‣ rs1 ▷ rs2

map-π₁ : {t u : Γ ⊢ σ ẋ τ} → t ⟶⋆ u → π₁ t ⟶⋆ π₁ u
map-π₁ ✦ = ✦
map-π₁ (r ‣ rs) =  ξ-π₁ r ‣ map-π₁ rs

map-π₂ : {t u : Γ ⊢ σ ẋ τ} → t ⟶⋆ u → π₂ t ⟶⋆ π₂ u
map-π₂ ✦ = ✦
map-π₂ (r ‣ rs) = ξ-π₂ r ‣ map-π₂ rs

map-pair : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t ⟶⋆ t' → s ⟶⋆ s' → (t , s) ⟶⋆ (t' , s')
map-pair ✦ ✦ = ✦
map-pair ✦ (r ‣ rs) = ξ-pair (same refl) r ‣ map-pair ✦ rs
map-pair (r ‣ rs) ✦ = ξ-pair r (same refl) ‣ map-pair rs ✦
map-pair (r₁ ‣ rs₁) (r₂ ‣ rs₂) = ξ-pair r₁ r₂ ‣ map-pair rs₁ rs₂

map-app : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t ⟶⋆ t' → s ⟶⋆ s' → (t · s) ⟶⋆ (t' · s')
map-app ✦ ✦ = ✦
map-app ✦ (r ‣ rs) = ξ-app (same refl) r ‣ map-app ✦ rs
map-app (r ‣ rs) ✦ = ξ-app r (same refl) ‣ map-app rs ✦ 
map-app (r₁ ‣ rs₁) (r₂ ‣ rs₂) = ξ-app r₁ r₂ ‣ map-app rs₁ rs₂

map-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t ⟶⋆ t' → (ƛ t) ⟶⋆ (ƛ t')
map-ƛ ✦ = ✦
map-ƛ (r ‣ rs) = ξ-ƛ r ‣ map-ƛ rs

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
map-rename ρ ✦ = ✦
map-rename ρ (r ‣ rs) = rename-ξ ρ r ‣ map-rename ρ rs

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
map-subst ts ✦ = ✦
map-subst ts (r ‣ rs) = subst-ξ ts r ‣ map-subst ts rs

data _⭆*_ : Sub Γ Δ → Sub Γ Δ → Set where
   [] : {ts ts' : Sub [] Δ} → ts ⭆* ts'
   _∷_ : {t t' : Δ ⊢ σ}{ts ts' : Sub Γ Δ} → t ⟶⋆ t' → ts ⭆* ts' → (t ∷ ts) ⭆* (t' ∷ ts')

lookup⭆* : {ts ts' : Sub Γ Δ} → ∀{σ} → (x : Γ ∋ σ) → ts ⭆* ts' → lookup x ts ⟶⋆ lookup x ts'
lookup⭆* ze (r ∷ _) = r
lookup⭆* (su x) (_ ∷ rs) = lookup⭆* x rs

mapSub⭆* : {f : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ} → (∀{σ} → {t t' : Δ ⊢ σ} → t ⟶⋆ t' → f t ⟶⋆ f t') → {ts ts' : Sub Γ Δ} → ts ⭆* ts' → mapSub f ts ⭆* mapSub f ts'
mapSub⭆* psv [] = []
mapSub⭆* psv (r ∷ rs) = psv r ∷ mapSub⭆* psv rs

_⟰* : ∀{σ} → {ts ts' : Sub Γ Δ} → ts ⭆* ts' → (_↑ {σ = σ} ts) ⭆* (ts' ↑)
rs ⟰* = ✦ ∷ mapSub⭆* (map-rename wk) rs

map-subst-Sub : (t : Γ ⊢ σ){ts ts' : Sub Γ Δ} → ts ⭆* ts' → subst t ts ⟶⋆ subst t ts'
map-subst-Sub (` x) rs = lookup⭆* x rs 
map-subst-Sub yes rs = ✦
map-subst-Sub no rs = ✦
map-subst-Sub ⟨⟩ rs = ✦
map-subst-Sub (t , s) rs = map-pair (map-subst-Sub t rs) (map-subst-Sub s rs)
map-subst-Sub (π₁ t) rs = map-π₁ (map-subst-Sub t rs)
map-subst-Sub (π₂ t) rs = map-π₂ (map-subst-Sub t rs)
map-subst-Sub (t · s) rs = map-app (map-subst-Sub t rs) (map-subst-Sub s rs)
map-subst-Sub (ƛ t) rs = map-ƛ (map-subst-Sub t (rs ⟰*))

idSub⭆*idSub : ∀{Γ} → idSub {Γ} ⭆* idSub
idSub⭆*idSub {[]} = []
idSub⭆*idSub {σ ∷ Γ} = idSub⭆*idSub ⟰*

map-/x : (t : σ ∷ Γ ⊢ τ){s s' : Γ ⊢ σ} → s ⟶⋆ s' → (t [ s /x]) ⟶⋆ (t [ s' /x])
map-/x t rs = map-subst-Sub t (rs ∷ idSub⭆*idSub)