module NaïveCanonicity where

open import Prelude
open import STLC
open import STLC.Reduction


-- closed term substitution
_[_] :  Γ ⊢ σ → Sub Γ [] → [] ⊢ σ
t [ ts ] = subst t ts

-- Define computability structure of canonicity for each type
Comp : (σ : Type) → [] ⊢ σ → Set
Comp Ans t = (t →β* yes) ⊎ (t →β* no)
Comp 𝟙 t = ⊤
Comp (σ ẋ τ) t = Comp σ (π₁ t) × Comp τ (π₂ t)
Comp (σ ⇒ τ) t = (a : [] ⊢ σ)(c : Comp σ a) → Comp τ (t · a)

-- Shift computability structure by β-reduction
comp-backward : (σ : Type){t t' : [] ⊢ σ} → t →β t' → Comp σ t' → Comp σ t
comp-backward Ans t→t' (inl t'→yes) = inl (t→t' ‣ t'→yes)
comp-backward Ans t→t' (inr t'→no) = inr (t→t' ‣ t'→no)
comp-backward 𝟙 t→t' _ = `nil
comp-backward (σ ẋ τ) t→t' (c₁ , c₂) = comp-backward σ (ξ-π₁ t→t') c₁ , comp-backward τ (ξ-π₂ t→t') c₂
comp-backward (σ ⇒ τ) t→t' c = λ a c' → comp-backward τ (ξ-·₁ t→t') (c a c')

-- list of corresponding computability structures for closed terms
data ⟦_⟧ᶜ : (Γ : Cxt) → Sub Γ [] → Set where
    [] : ⟦ [] ⟧ᶜ []
    _∷_ : ∀{σ} → {t : [] ⊢ σ}{ts : Sub Γ []} → Comp σ t → ⟦ Γ ⟧ᶜ ts → ⟦ (σ ∷ Γ) ⟧ᶜ (t ∷ ts)

lookupᶜ : {ts : Sub Γ []}(x : Γ ∋ σ) → ⟦ Γ ⟧ᶜ ts → Comp σ (lookup x ts)
lookupᶜ ze (c ∷ _) = c
lookupᶜ (su x) (_ ∷ cs) = lookupᶜ x cs

-- assign computability morphism for each term
⟦_⟧ : (t : Γ ⊢ σ)(ts : Sub Γ [])(cs : ⟦ Γ ⟧ᶜ ts) → Comp σ (t [ ts ])
⟦ ` x ⟧ ts cs = lookupᶜ x cs
⟦ yes ⟧ ts cs = inl ✦
⟦ no ⟧ ts cs = inr ✦
⟦ ⟨⟩ ⟧ ts cs = `nil
⟦ t , s ⟧ ts cs = comp-backward _ β-π₁ (⟦ t ⟧ ts cs) , comp-backward _ β-π₂ (⟦ s ⟧ ts cs)
⟦ π₁ t ⟧ ts cs = pr₁ (⟦ t ⟧ ts cs)
⟦ π₂ t ⟧ ts cs = pr₂ (⟦ t ⟧ ts cs)
⟦ t · s ⟧ ts cs = ⟦ t ⟧ ts cs (s [ ts ]) (⟦ s ⟧ ts cs)
⟦ ƛ t ⟧ ts cs = λ a c →  comp-backward _ β-ƛ (transport (Comp _) (≡-sym (lem[sub1] t ts a)) (⟦ t ⟧ (a ∷ ts) (c ∷ cs)))

-- empty substitution is identity
[[]] : (t : [] ⊢ σ) → (t [ [] ]) ≡ t
[[]] t = subst-idSub {t = t}

-- Proving canonicity
thm[canonicity] : (t : [] ⊢ Ans) → ([] ⊢ t ≐ yes ∶ Ans) ⊎ ([] ⊢ t ≐ no ∶ Ans)
thm[canonicity] t with ⟦ t ⟧ [] []
... | inl t[[]]→yes = inl (β-red (≡→β* ([[]] t) t[[]]→yes))
... | inr t[[]]→no  = inr (β-red (≡→β* ([[]] t) t[[]]→no))

test-term : [] ⊢ Ans
test-term = π₁ (yes , no)
    -- (ƛ (` ze)) · (π₁ (π₂ (yes , ((ƛ (` ze)) · no)) , ⟨⟩))

test-canonicity : ([] ⊢ test-term ≐ yes ∶ Ans) ⊎ ([] ⊢ test-term ≐ no ∶ Ans)
test-canonicity = thm[canonicity] test-term 