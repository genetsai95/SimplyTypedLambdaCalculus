module STLC.Renaming where

open import Prelude
open import STLC.Base
open import STLC.TermEquationalReasonings

-- renamings
_⊆_ : Cxt → Cxt → Set
Γ ⊆ Δ = ∀{σ} → Γ ∋ σ → Δ ∋ σ

data Ren : Cxt → Cxt → Set where
    [] : Ren [] Δ
    _∷_ : Δ ∋ σ → Ren Γ Δ → Ren (σ ∷ Γ) Δ

lookupRen : Γ ∋ σ → Ren Γ Δ → Δ ∋ σ
lookupRen ze (r ∷ rs) = r
lookupRen (su x) (r ∷ rs) = lookupRen x rs

mapRen : (∀{σ} → Δ ∋ σ → Θ ∋ σ) → Ren Γ Δ → Ren Γ Θ
mapRen f [] = []
mapRen f (r ∷ rs) = f r ∷ mapRen f rs

concatRen : Ren Γ Δ → Ren Δ Θ → Ren Γ Θ
concatRen ρ ρ' = mapRen (λ x → lookupRen x ρ') ρ

lift : Ren Γ Δ → Ren (σ ∷ Γ) (σ ∷ Δ)
lift rs = ze ∷ mapRen su rs

idRen : Ren Γ Γ
idRen {[]} = []
idRen {σ ∷ Γ} = lift idRen

rename : Ren Γ Δ → Γ ⊢ σ → Δ ⊢ σ
rename rs (` x) = ` lookupRen x rs
rename rs yes = yes
rename rs no = no
rename rs ⟨⟩ = ⟨⟩
rename rs (t , s) = rename rs t , rename rs s
rename rs (π₁ t) = π₁ (rename rs t)
rename rs (π₂ t) = π₂ (rename rs t)
rename rs (ƛ t) = ƛ rename (lift rs) t
rename rs (t · s) = rename rs t · rename rs s

ext : Γ ⊆ Δ → σ ∷ Γ ⊆ σ ∷ Δ
ext s ze = ze
ext s (su n) = su (s n)

pop : (σ ∷ Γ) ⊆ Δ → Γ ⊆ Δ
pop ρ n = ρ (su n)

rename' : Γ ⊆ Δ → Γ ⊢ σ → Δ ⊢ σ
rename' ρ (` x) = ` (ρ x)
rename' ρ yes = yes
rename' ρ no = no
rename' ρ ⟨⟩ = ⟨⟩
rename' ρ (t , s) = rename' ρ t , rename' ρ s
rename' ρ (π₁ t) = π₁ (rename' ρ t)
rename' ρ (π₂ t) = π₂ (rename' ρ t)
rename' ρ (t · s) = rename' ρ t · rename' ρ s
rename' ρ (ƛ t) = ƛ rename' (ext ρ) t

-- weakening
wk : Ren Γ (σ ∷ Γ)
wk = mapRen su idRen

weaken : Γ ⊢ σ → τ ∷ Γ ⊢ σ
weaken = rename wk 

weaken' : Γ ⊢ σ → τ ∷ Γ ⊢ σ
weaken' = rename' su

-- equalities about renamings
∷-ren-eq : {x y : Δ ∋ σ}{xs ys : Ren Γ Δ} → x ≡ y → xs ≡ ys → _≡_ {X = Ren (σ ∷ Γ) Δ} (x ∷ xs) (y ∷ ys)
∷-ren-eq refl refl = refl

ren-head-eq-elim : {x : Δ ∋ σ}{xs ys : Ren Γ Δ} → _≡_ {X = Ren (σ ∷ Γ) Δ} (x ∷ xs) (x ∷ ys) → xs ≡ ys
ren-head-eq-elim refl = refl

lookupRen-map : (f : ∀{τ} → Δ ∋ τ → Θ ∋ τ){rs : Ren Γ Δ}(x : Γ ∋ σ){t : Δ ∋ σ} → lookupRen x rs ≡ t → lookupRen x (mapRen f rs) ≡ f t
lookupRen-map f {_ ∷ _} ze refl = refl
lookupRen-map f {_ ∷ rs} (su x) refl = lookupRen-map f {rs} x refl

lookupRen-idRen : (x : Γ ∋ σ) → lookupRen x idRen ≡ x
lookupRen-idRen ze = refl
lookupRen-idRen (su x) = lookupRen-map su x (lookupRen-idRen x)

rename-idRen : (t : Γ ⊢ σ) → rename idRen t ≡ t
rename-idRen (` x) = cong `_ (lookupRen-idRen x)
rename-idRen yes = refl
rename-idRen no = refl
rename-idRen ⟨⟩ = refl
rename-idRen (t , s) = pair-term-≡ (rename-idRen t) (rename-idRen s)
rename-idRen (π₁ t) = cong π₁ (rename-idRen t)
rename-idRen (π₂ t) = cong π₂ (rename-idRen t)
rename-idRen (ƛ t) = cong ƛ_ (rename-idRen t)
rename-idRen (t · s) = app-term-≡ (rename-idRen t) (rename-idRen s)

rename'≡rename : {ρ : Γ ⊆ Δ}{rs : Ren Γ Δ} → (∀{τ} → (x : Γ ∋ τ) → ρ x ≡ lookupRen x rs) → (t : Γ ⊢ σ) → rename' ρ t ≡ rename rs t
rename'≡rename eq (` x) = cong `_ (eq x)
rename'≡rename _ yes = refl
rename'≡rename _ no = refl
rename'≡rename _ ⟨⟩ = refl
rename'≡rename eq (t , s) = pair-term-≡ (rename'≡rename eq t) (rename'≡rename eq s)
rename'≡rename eq (π₁ t) = cong π₁ (rename'≡rename eq t)
rename'≡rename eq (π₂ t) = cong π₂ (rename'≡rename eq t)
rename'≡rename eq (t · s) = app-term-≡ (rename'≡rename eq t) (rename'≡rename eq s)
rename'≡rename eq (ƛ t) = cong ƛ_ (rename'≡rename (ext≡lift eq) t)
    where
        ext≡lift : {ρ : Γ ⊆ Δ}{rs : Ren Γ Δ} → (∀{σ} → (x : Γ ∋ σ) → ρ x ≡ lookupRen x rs) → {σ τ : Type}(x : τ ∷ Γ ∋ σ) → ext ρ x ≡ lookupRen x (lift rs)
        ext≡lift eq ze = refl
        ext≡lift {ρ = ρ} {rs = rs} eq (su x) = ≡-sym (lookupRen x (mapRen su rs) ≡⟨ lookupRen-map su x (≡-sym (eq x)) ⟩ su (ρ x) ∎)

lookupRen-wk : ∀{τ} → (x : Γ ∋ σ) → lookupRen x (wk {Γ} {τ}) ≡ su x
lookupRen-wk ze = refl
lookupRen-wk (su x) = lookupRen-map su x (lookupRen-wk x)

wk≡su : ∀{τ} → (x : Γ ∋ σ) → lookupRen x (wk {Γ} {τ}) ≡ su x
wk≡su ze = refl
wk≡su (su x) = lookupRen-map su x (wk≡su x)

weaken≡weaken' : ∀{τ} → (t : Γ ⊢ σ) → weaken {τ = τ} t ≡ weaken' t
weaken≡weaken' t = ≡-sym (rename'≡rename (λ x → ≡-sym (wk≡su x)) t)

concatRen-lift : ∀{σ} → (ρ : Ren Γ Δ)(ρ' : Ren Δ Θ) → concatRen (lift {σ = σ} ρ) (lift ρ') ≡ lift (concatRen ρ ρ')
concatRen-lift [] ρ' = refl 
concatRen-lift (r ∷ ρ) ρ' = cong (ze ∷_) (∷-ren-eq (lookupRen-map su r refl) (ren-head-eq-elim (concatRen-lift ρ ρ'))) 