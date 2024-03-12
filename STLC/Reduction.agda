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

ξ-π₁* : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₁ t →β* π₁ u
ξ-π₁* ✦ = ✦
ξ-π₁* (r ‣ rs) = ξ-π₁ r ‣ ξ-π₁* rs

ξ-π₂* : {t u : Γ ⊢ σ ẋ τ} → t →β* u → π₂ t →β* π₂ u
ξ-π₂* ✦ = ✦
ξ-π₂* (r ‣ rs) = ξ-π₂ r ‣ ξ-π₂* rs

ξ-pair* : {t t' : Γ ⊢ σ}{s s' : Γ ⊢ τ} → t →β* t' → s →β* s' → (t , s) →β* (t' , s')
ξ-pair* ✦ ✦ = ✦
ξ-pair* ✦ (r ‣ rs) = ξ-pair (same refl) r ‣ ξ-pair* ✦ rs
ξ-pair* (r ‣ rs) ✦ = ξ-pair r (same refl) ‣ ξ-pair* rs ✦
ξ-pair* (r₁ ‣ rs₁) (r₂ ‣ rs₂) = ξ-pair r₁ r₂ ‣ ξ-pair* rs₁ rs₂

ξ-app* : {t t' : Γ ⊢ σ ⇒ τ}{s s' : Γ ⊢ σ} → t →β* t' → s →β* s' → (t · s) →β* (t' · s')
ξ-app* ✦ ✦ = ✦
ξ-app* ✦ (r ‣ rs) = ξ-app (same refl) r ‣ ξ-app* ✦ rs
ξ-app* (r ‣ rs) ✦ = ξ-app r (same refl) ‣ ξ-app* rs ✦  
ξ-app* (r₁ ‣ rs₁) (r₂ ‣ rs₂) = ξ-app r₁ r₂ ‣ ξ-app* rs₁ rs₂

ξ-ƛ* : {t t' : σ ∷ Γ ⊢ τ} → t →β* t' → (ƛ t) →β* (ƛ t')
ξ-ƛ* ✦ = ✦
ξ-ƛ* (r ‣ rs) = ξ-ƛ r ‣ ξ-ƛ* rs

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

rename-ξ* : (ρ : Ren Γ Δ){t t' : Γ ⊢ σ} → t →β* t' → rename ρ t →β* rename ρ t'
rename-ξ* ρ ✦ = ✦
rename-ξ* ρ (r ‣ rs) = rename-ξ ρ r ‣ rename-ξ* ρ rs

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

subst-ξ* : (ts : Sub Γ Δ){t t' : Γ ⊢ σ} → t →β* t' → subst t ts →β* subst t' ts
subst-ξ* ts ✦ = ✦
subst-ξ* ts (r ‣ rs) = subst-ξ ts r ‣ subst-ξ* ts rs


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
subst-Sub-ξ (` x) rs = lookup⇛β x rs
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

/x-ξ* : (t : σ ∷ Γ ⊢ τ){s s' : Γ ⊢ σ} → s →β* s' → (t [ s /x]) →β* (t [ s' /x])
/x-ξ* t ✦ = ✦
/x-ξ* t (r ‣ rs) = /x-ξ t r ‣ /x-ξ* t rs

data _⇛β*_ : Sub Γ Δ → Sub Γ Δ → Set where
   [] : {ts ts' : Sub [] Δ} → ts ⇛β* ts'
   _∷_ : {t t' : Δ ⊢ σ}{ts ts' : Sub Γ Δ} → t →β* t' → ts ⇛β* ts' → (t ∷ ts) ⇛β* (t' ∷ ts')

lookup⇛β* : {ts ts' : Sub Γ Δ}{σ : Type}(x : Γ ∋ σ) → ts ⇛β* ts' → lookup x ts →β* lookup x ts'
lookup⇛β* ze (r ∷ _) = r
lookup⇛β* (su x) (_ ∷ rs) = lookup⇛β* x rs 

_✴ : {ts ts' : Sub Γ Δ} → ts ⇛β ts' → ts ⇛β* ts'
[] ✴ = []
(r ∷ rs) ✴ = (r ‣ ✦) ∷ (rs ✴)

✦✦ : {ts : Sub Γ Δ} → ts ⇛β* ts
✦✦ {ts = []} = [] 
✦✦ {ts = t ∷ ts} = ✦ ∷ ✦✦

_‣‣_ : {ts ts' ts'' : Sub Γ Δ} → ts ⇛β ts' → ts' ⇛β* ts'' → ts ⇛β* ts''
[] ‣‣ _ = [] 
(r ∷ rs) ‣‣ (r' ∷ rs') = (r ‣ r') ∷ (rs ‣‣ rs')

_▷▷_ : {ts ts' ts'' : Sub Γ Δ} → ts ⇛β* ts' → ts' ⇛β* ts'' → ts ⇛β* ts''
[] ▷▷ _ = []
(r₁ ∷ rs₁) ▷▷ (r₂ ∷ rs₂) = (r₁ ▷ r₂) ∷ (rs₁ ▷▷ rs₂)

mapSub⇛β* : {f : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ} → (∀{σ} → {t t' : Δ ⊢ σ} → t →β* t' → f t →β* f t') → {ts ts' : Sub Γ Δ} → ts ⇛β* ts' → mapSub f ts ⇛β* mapSub f ts'
mapSub⇛β* psv [] = []
mapSub⇛β* psv (r ∷ rs) = psv r ∷ mapSub⇛β* psv rs

_⤊β* : ∀{σ} → {ts ts' : Sub Γ Δ} → ts ⇛β* ts' → (_↑ {σ = σ} ts) ⇛β* (ts' ↑)
rs ⤊β* = ✦ ∷ mapSub⇛β* (rename-ξ* wk) rs

idSub⇛β*idSub : ∀{Γ} → idSub {Γ} ⇛β* idSub
idSub⇛β*idSub = idSub⇛βidSub ✴

subst-ξ*-Sub : (t : Γ ⊢ σ){ts ts' : Sub Γ Δ} → ts ⇛β* ts' → subst t ts →β* subst t ts'
subst-ξ*-Sub (` x) rs = lookup⇛β* x rs 
subst-ξ*-Sub yes rs = ✦
subst-ξ*-Sub no rs = ✦
subst-ξ*-Sub ⟨⟩ rs = ✦
subst-ξ*-Sub (t , s) rs = ξ-pair* (subst-ξ*-Sub t rs) (subst-ξ*-Sub s rs)
subst-ξ*-Sub (π₁ t) rs = ξ-π₁* (subst-ξ*-Sub t rs)
subst-ξ*-Sub (π₂ t) rs = ξ-π₂* (subst-ξ*-Sub t rs)
subst-ξ*-Sub (t · s) rs = ξ-app* (subst-ξ*-Sub t rs) (subst-ξ*-Sub s rs)
subst-ξ*-Sub (ƛ t) rs = ξ-ƛ* (subst-ξ*-Sub t (rs ⤊β*))