module STLC.Conversion where

open import Prelude
open import STLC.Base
open import STLC.Renaming
open import STLC.Substitution
open import STLC.Lemmas

data _⟶_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₁ (t , s) ⟶ t
    β-π₂ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₂ (t , s) ⟶ s
    ξ-,₁ : {t t' : Γ ⊢ σ}{s : Γ ⊢ τ} → t ⟶ t' → (t , s) ⟶ (t' , s)
    ξ-,₂ : {t : Γ ⊢ σ}{s s' : Γ ⊢ τ} → s ⟶ s' → (t , s) ⟶ (t , s')
    ξ-π₁ : {t t' : Γ ⊢ σ ẋ τ} → t ⟶ t' → π₁ t ⟶ π₁ t'
    ξ-π₂ : {t t' : Γ ⊢ σ ẋ τ} → t ⟶ t' → π₂ t ⟶ π₂ t'
    η-, : {t : Γ ⊢ σ ẋ τ} → t ⟶ (π₁ t , π₂ t)

    β-ƛ : {t : σ ∷ Γ ⊢ τ}{s : Γ ⊢ σ} → (ƛ t) · s ⟶ t [ s /x]
    ξ-·₁ : {t t' : Γ ⊢ σ ⇒ τ}{s : Γ ⊢ σ} → t ⟶ t' → t · s ⟶ t' · s
    ξ-·₂ : {t : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → s ⟶ s' → t · s ⟶ t · s'
    ξ-ƛ : {t t' : σ ∷ Γ ⊢ τ} → t ⟶ t' → (ƛ t) ⟶ (ƛ t')
    η-ƛ : {t : Γ ⊢ σ ⇒ τ} → t ⟶ (ƛ (weaken {τ = σ} t · (` ze)))

    η-⟨⟩ : {t : Γ ⊢ 𝟙} → t ⟶ ⟨⟩

infixr 33 _‣_
data _⟶⋆_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    ✦ : {t : Γ ⊢ σ} → t ⟶⋆ t
    _‣_ : {t u v : Γ ⊢ σ} → t ⟶ u → u ⟶⋆ v → t ⟶⋆ v

infixr 35 _▷_
_▷_ : {t u v : Γ ⊢ σ} → t ⟶⋆ u → u ⟶⋆ v → t ⟶⋆ v
✦ ▷ rs = rs
(r ‣ rs1) ▷ rs2 = r ‣ rs1 ▷ rs2

map⟶⋆ : ∀{Γ Δ σ τ} → (f : Γ ⊢ σ → Δ ⊢ τ) → ({t t' : Γ ⊢ σ} → t ⟶ t' → f t ⟶ f t') → {t t' : Γ ⊢ σ} → t ⟶⋆ t' → f t ⟶⋆ f t'
map⟶⋆ f ξ ✦ = ✦
map⟶⋆ f ξ (r ‣ rs) = ξ r ‣ map⟶⋆ f ξ rs 

ξ-π₁⋆ : {t u : Γ ⊢ σ ẋ τ} → t ⟶⋆ u → π₁ t ⟶⋆ π₁ u
ξ-π₁⋆ = map⟶⋆ π₁ ξ-π₁

ξ-π₂⋆ : {t u : Γ ⊢ σ ẋ τ} → t ⟶⋆ u → π₂ t ⟶⋆ π₂ u
ξ-π₂⋆ = map⟶⋆ π₂ ξ-π₂

ξ-,⋆ : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t ⟶⋆ t' → s ⟶⋆ s' → (t , s) ⟶⋆ (t' , s')
ξ-,⋆ {t = t} {t'} {s} {s'} t→t' s→s' = map⟶⋆ (_, s) ξ-,₁ t→t' ▷ map⟶⋆ (t' ,_) ξ-,₂ s→s'

ξ-·⋆ : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t ⟶⋆ t' → s ⟶⋆ s' → (t · s) ⟶⋆ (t' · s')
ξ-·⋆ {t = t} {t'} {s} {s'} t→t' s→s' = map⟶⋆ (_· s) ξ-·₁ t→t' ▷ map⟶⋆ (t' ·_) ξ-·₂ s→s'

ξ-ƛ⋆ : {t t' : σ ∷ Γ ⊢ τ} → t ⟶⋆ t' → (ƛ t) ⟶⋆ (ƛ t')
ξ-ƛ⋆ = map⟶⋆ ƛ_ ξ-ƛ

≡⟶ : {t t' s : Γ ⊢ σ} → t ≡ t' → t ⟶ s → t' ⟶ s
≡⟶ refl t→s = t→s

⟶≡ : {t s s' : Γ ⊢ σ} → s ≡ s' → t ⟶ s → t ⟶ s'
⟶≡ refl t→s = t→s

≡⟶⋆ : {t t' s : Γ ⊢ σ} → t ≡ t' → t ⟶⋆ s → t' ⟶⋆ s
≡⟶⋆ refl t→s = t→s

⟶⋆≡ : {t s s' : Γ ⊢ σ} → s ≡ s' → t ⟶⋆ s → t ⟶⋆ s'
⟶⋆≡ refl t→s = t→s

ξ-rename : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t ⟶ t' → rename ρ t ⟶ rename ρ t'
ξ-rename ρ β-π₁ = β-π₁
ξ-rename ρ β-π₂ = β-π₂
ξ-rename ρ (ξ-,₁ t→t') = ξ-,₁ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-,₂ t→t') = ξ-,₂ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-π₁ t→t') = ξ-π₁ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-π₂ t→t') = ξ-π₂ (ξ-rename ρ t→t')
ξ-rename ρ η-, = η-,
ξ-rename ρ {(ƛ t) · s} {t'} β-ƛ = ⟶≡ (subst-rename≡rename-subst ρ t {s}) β-ƛ
ξ-rename ρ (ξ-·₁ t→t') = ξ-·₁ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-·₂ t→t') = ξ-·₂ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-ƛ t→t') = ξ-ƛ (ξ-rename (lift ρ) t→t')
ξ-rename ρ {t} η-ƛ = ⟶≡ (cong (λ y → ƛ (y · (` ze))) (≡-sym (rename-lift-weaken≡weaken-rename ρ t))) η-ƛ
ξ-rename ρ η-⟨⟩ = η-⟨⟩

ξ-rename⋆ : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t ⟶⋆ t' → rename ρ t ⟶⋆ rename ρ t'
ξ-rename⋆ ρ = map⟶⋆ (rename ρ) (ξ-rename ρ)

ξ-subst : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t ⟶ t' → subst t ts ⟶ subst t' ts
ξ-subst ts β-π₁ = β-π₁
ξ-subst ts β-π₂ = β-π₂
ξ-subst ts (ξ-,₁ t→t') = ξ-,₁ (ξ-subst ts t→t')
ξ-subst ts (ξ-,₂ t→t') = ξ-,₂ (ξ-subst ts t→t')
ξ-subst ts (ξ-π₁ t→t') = ξ-π₁ (ξ-subst ts t→t')
ξ-subst ts (ξ-π₂ t→t') = ξ-π₂ (ξ-subst ts t→t')
ξ-subst ts η-, = η-,
ξ-subst ts {(ƛ t) · s} β-ƛ = ⟶≡ eq β-ƛ
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
ξ-subst ts (ξ-·₁ t→t') = ξ-·₁ (ξ-subst ts t→t')
ξ-subst ts (ξ-·₂ t→t') = ξ-·₂ (ξ-subst ts t→t')
ξ-subst ts (ξ-ƛ t→t') = ξ-ƛ (ξ-subst (ts ↑) t→t')
ξ-subst ts {t} η-ƛ = ⟶≡ (cong (λ y → ƛ (y · (` ze))) (≡-sym (subst-weaken-↑ t ts))) η-ƛ
ξ-subst ts η-⟨⟩ = η-⟨⟩

ξ-subst⋆ : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t ⟶⋆ t' → subst t ts ⟶⋆ subst t' ts
ξ-subst⋆ ts = map⟶⋆ (λ t → subst t ts) (ξ-subst ts)

data _⭆*_ : Sub Γ Δ → Sub Γ Δ → Set where
   [] : {ts ts' : Sub [] Δ} → ts ⭆* ts'
   _∷_ : {t t' : Δ ⊢ σ}{ts ts' : Sub Γ Δ} → t ⟶⋆ t' → ts ⭆* ts' → (t ∷ ts) ⭆* (t' ∷ ts')

lookup⭆* : {ts ts' : Sub Γ Δ} → ∀{σ} → (x : Γ ∋ σ) → ts ⭆* ts' → lookup x ts ⟶⋆ lookup x ts'
lookup⭆* ze (r ∷ _) = r
lookup⭆* (su x) (_ ∷ rs) = lookup⭆* x rs

map⭆* : {f : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ} → (∀{σ} → {t t' : Δ ⊢ σ} → t ⟶⋆ t' → f t ⟶⋆ f t') → {ts ts' : Sub Γ Δ} → ts ⭆* ts' → mapSub f ts ⭆* mapSub f ts'
map⭆* psv [] = []
map⭆* psv (r ∷ rs) = psv r ∷ map⭆* psv rs

_⟰* : ∀{σ} → {ts ts' : Sub Γ Δ} → ts ⭆* ts' → (_↑ {σ = σ} ts) ⭆* (ts' ↑)
rs ⟰* = ✦ ∷ map⭆* (ξ-rename⋆ wk) rs

ξ-⭆* : (t : Γ ⊢ σ){ts ts' : Sub Γ Δ} → ts ⭆* ts' → subst t ts ⟶⋆ subst t ts'
ξ-⭆* (` x) rs = lookup⭆* x rs
ξ-⭆* yes rs = ✦
ξ-⭆* no rs = ✦
ξ-⭆* ⟨⟩ rs = ✦
ξ-⭆* (t , s) rs = ξ-,⋆ (ξ-⭆* t rs) (ξ-⭆* s rs)
ξ-⭆* (π₁ t) rs = ξ-π₁⋆ (ξ-⭆* t rs)
ξ-⭆* (π₂ t) rs = ξ-π₂⋆ (ξ-⭆* t rs)
ξ-⭆* (t · s) rs = ξ-·⋆ (ξ-⭆* t rs) (ξ-⭆* s rs)
ξ-⭆* (ƛ t) rs = ξ-ƛ⋆ (ξ-⭆* t (rs ⟰*))

idSub⭆*idSub : ∀{Γ} → idSub {Γ} ⭆* idSub
idSub⭆*idSub {[]} = []
idSub⭆*idSub {σ ∷ Γ} = idSub⭆*idSub ⟰*

ξ-/x⋆ : (t : σ ∷ Γ ⊢ τ){s s' : Γ ⊢ σ} → s ⟶⋆ s' → (t [ s /x]) ⟶⋆ (t [ s' /x])
ξ-/x⋆ t rs = ξ-⭆* t (rs ∷ idSub⭆*idSub)