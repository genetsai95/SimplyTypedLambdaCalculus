module STLC.Reduction where

open import Prelude
open import STLC.Base
open import STLC.Renaming
open import STLC.Substitution
open import STLC.Lemmas


-- definition of β-reduction
data _→β_ : Γ ⊢ σ → Γ ⊢ σ → Set where
    β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₁ (t , s) →β t
    β-π₂ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₂ (t , s) →β s
    ξ-,₁ : {t t' : Γ ⊢ σ}{s : Γ ⊢ τ} → t →β t' → (t , s) →β (t' , s)
    ξ-,₂ : {t : Γ ⊢ σ}{s s' : Γ ⊢ τ} → s →β s' → (t , s) →β (t , s')
    ξ-π₁ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₁ t →β π₁ t'
    ξ-π₂ : {t t' : Γ ⊢ σ ẋ τ} → t →β t' → π₂ t →β π₂ t'

    β-ƛ : {t : σ ∷ Γ ⊢ τ}{s : Γ ⊢ σ} → (ƛ t) · s →β t [ s /x]
    ξ-·₁ : {t t' : Γ ⊢ σ ⇒ τ}{s : Γ ⊢ σ} → t →β t' → t · s →β t' · s
    ξ-·₂ : {t : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → s →β s' → t · s →β t · s'
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
map→β* : ∀{Γ Δ σ τ} → (f : Γ ⊢ σ → Δ ⊢ τ) → ({t t' : Γ ⊢ σ} → t →β t' → f t →β f t') → {t t' : Γ ⊢ σ} → t →β* t' → f t →β* f t'
map→β* f ξ ✦ = ✦
map→β* f ξ (r ‣ rs) = ξ r ‣ map→β* f ξ rs 

ξ-π₁* : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₁ t →β* π₁ u
ξ-π₁* = map→β* π₁ ξ-π₁

ξ-π₂* : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₂ t →β* π₂ u
ξ-π₂* = map→β* π₂ ξ-π₂

ξ-,* : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t →β* t' → s →β* s' → (t , s) →β* (t' , s')
ξ-,* {t = t} {t'} {s} {s'} t→t' s→s' = map→β* (_, s) ξ-,₁ t→t' ▷ map→β* (t' ,_) ξ-,₂ s→s'

ξ-·* : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t →β* t' → s →β* s' → (t · s) →β* (t' · s')
ξ-·* {t = t} {t'} {s} {s'} t→t' s→s' = map→β* (_· s) ξ-·₁ t→t' ▷ map→β* (t' ·_) ξ-·₂ s→s'

ξ-ƛ* : {t t' : σ ∷ Γ ⊢ τ} → t →β* t' → (ƛ t) →β* (ƛ t')
ξ-ƛ* = map→β* ƛ_ ξ-ƛ

≡→β : {t t' s : Γ ⊢ σ} → t ≡ t' → t →β s → t' →β s
≡→β refl t→s = t→s

→β≡ : {t s s' : Γ ⊢ σ} → s ≡ s' → t →β s → t →β s'
→β≡ refl t→s = t→s

≡→β* : {t t' s : Γ ⊢ σ} → t ≡ t' → t →β* s → t' →β* s
≡→β* refl t→s = t→s

→β*≡ : {t s s' : Γ ⊢ σ} → s ≡ s' → t →β* s → t →β* s'
→β*≡ refl t→s = t→s

ξ-rename : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t →β t' → rename ρ t →β rename ρ t'
ξ-rename ρ β-π₁ = β-π₁
ξ-rename ρ β-π₂ = β-π₂
ξ-rename ρ (ξ-,₁ t→t') = ξ-,₁ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-,₂ t→t') = ξ-,₂ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-π₁ t→t') = ξ-π₁ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-π₂ t→t') = ξ-π₂ (ξ-rename ρ t→t')
ξ-rename ρ {(ƛ t) · s} {t'} β-ƛ = →β≡ (subst-rename≡rename-subst ρ t {s}) β-ƛ
ξ-rename ρ (ξ-·₁ t→t') = ξ-·₁ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-·₂ t→t') = ξ-·₂ (ξ-rename ρ t→t')
ξ-rename ρ (ξ-ƛ t→t') = ξ-ƛ (ξ-rename (lift ρ) t→t')

ξ-rename* : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t →β* t' → rename ρ t →β* rename ρ t'
ξ-rename* ρ = map→β* (rename ρ) (ξ-rename ρ)

ξ-subst : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t →β t' → subst t ts →β subst t' ts
ξ-subst ts β-π₁ = β-π₁
ξ-subst ts β-π₂ = β-π₂
ξ-subst ts (ξ-,₁ t→t') = ξ-,₁ (ξ-subst ts t→t')
ξ-subst ts (ξ-,₂ t→t') = ξ-,₂ (ξ-subst ts t→t')
ξ-subst ts (ξ-π₁ t→t') = ξ-π₁ (ξ-subst ts t→t')
ξ-subst ts (ξ-π₂ t→t') = ξ-π₂ (ξ-subst ts t→t')
ξ-subst ts {(ƛ t) · s} β-ƛ = →β≡ eq β-ƛ
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

ξ-subst* : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t →β* t' → subst t ts →β* subst t' ts
ξ-subst* ts = map→β* (λ t → subst t ts) (ξ-subst ts)


-- β-reduction of substitutions
data _⇛β*_ : Sub Γ Δ → Sub Γ Δ → Set where
   [] : {ts ts' : Sub [] Δ} → ts ⇛β* ts'
   _∷_ : {t t' : Δ ⊢ σ}{ts ts' : Sub Γ Δ} → t →β* t' → ts ⇛β* ts' → (t ∷ ts) ⇛β* (t' ∷ ts')

lookup⇛β* : {ts ts' : Sub Γ Δ}{σ : Type}(x : Γ ∋ σ) → ts ⇛β* ts' → lookup x ts →β* lookup x ts'
lookup⇛β* ze (r ∷ _) = r
lookup⇛β* (su x) (_ ∷ rs) = lookup⇛β* x rs

map⇛β* : {f : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ} → (∀{σ} → {t t' : Δ ⊢ σ} → t →β* t' → f t →β* f t') → {ts ts' : Sub Γ Δ} → ts ⇛β* ts' → mapSub f ts ⇛β* mapSub f ts'
map⇛β* psv [] = []
map⇛β* psv (r ∷ rs) = psv r ∷ map⇛β* psv rs

_⤊β* : ∀{σ} → {ts ts' : Sub Γ Δ} → ts ⇛β* ts' → (_↑ {σ = σ} ts) ⇛β* (ts' ↑)
rs ⤊β* = ✦ ∷ map⇛β* (ξ-rename* wk) rs

idSub⇛β*idSub : ∀{Γ} → idSub {Γ} ⇛β* idSub
idSub⇛β*idSub {[]} = []
idSub⇛β*idSub {σ ∷ Γ} = idSub⇛β*idSub ⤊β*

ξ-⇛β* : (t : Γ ⊢ σ){ts ts' : Sub Γ Δ} → ts ⇛β* ts' → subst t ts →β* subst t ts'
ξ-⇛β* (` x) rs = lookup⇛β* x rs
ξ-⇛β* yes rs = ✦
ξ-⇛β* no rs = ✦
ξ-⇛β* ⟨⟩ rs = ✦
ξ-⇛β* (t , s) rs = ξ-,* (ξ-⇛β* t rs) (ξ-⇛β* s rs)
ξ-⇛β* (π₁ t) rs = ξ-π₁* (ξ-⇛β* t rs)
ξ-⇛β* (π₂ t) rs = ξ-π₂* (ξ-⇛β* t rs)
ξ-⇛β* (t · s) rs = ξ-·* (ξ-⇛β* t rs) (ξ-⇛β* s rs)
ξ-⇛β* (ƛ t) rs = ξ-ƛ* (ξ-⇛β* t (rs ⤊β*))