module NaïveCanonicity' where

open import Prelude
open import STLC

-- context -> list of closed terms with corresponding types
⟦_⟧ᶜ : Cxt → Set
⟦ Γ ⟧ᶜ = Sub Γ []


-- closed term substitution
_[_] :  Γ ⊢ σ → ⟦ Γ ⟧ᶜ → [] ⊢ σ
t [ ts ] = subst t ts

-- computability structure

Comp : (σ : Type) → [] ⊢ σ → Set
Comp Ans t = (t →β* yes) ⊎ (t →β* no)
Comp 𝟙 t = ⊤
Comp (σ ⇒ τ) t = Σ (σ ∷ [] ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((a : [] ⊢ σ)(u : Comp σ a) → Comp τ (t' [ a /x])))
Comp (σ ẋ τ) t = 
            -- Comp σ (π₁ t) × Comp τ (π₂ t) 
            -- Σ ([] ⊢ σ) (λ t' → Σ ([] ⊢ τ) (λ t'' → ((π₁ t →β* t') × (π₂ t →β* t'') × Comp σ t' × Comp τ t'')))
            Σ ([] ⊢ σ) (λ t' → Σ ([] ⊢ τ) (λ t'' → ((t →β* (t' , t'')) × Comp σ t' × Comp τ t'')))

-- context -> corresponding computability structures for closed terms
data ⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ → Set where
    [] : ⟦ [] ⟧ˢ []
    _∷_ : ∀{σ} → {t : [] ⊢ σ}{ts : ⟦ Γ ⟧ᶜ} → Comp σ t → ⟦ Γ ⟧ˢ ts → ⟦ (σ ∷ Γ) ⟧ˢ (t ∷ ts)

lookupˢ : {ts : ⟦ Γ ⟧ᶜ}(x : Γ ∋ σ) → ⟦ Γ ⟧ˢ ts → Comp σ (lookup x ts)
lookupˢ ze (c ∷ _) = c
lookupˢ (su x) (_ ∷ cs) = lookupˢ x cs



-- computability morphism
⟦_⟧ : (t : Γ ⊢ σ) → (ts : ⟦ Γ ⟧ᶜ)(cs : ⟦ Γ ⟧ˢ ts) → Comp σ (t [ ts ])
⟦ ` x ⟧ ts cs = lookupˢ x cs
⟦ yes ⟧ ts cs = inl β-base
⟦ no ⟧ ts cs = inr β-base
⟦ ⟨⟩ ⟧ ts cs = `nil
⟦ t , s ⟧ ts cs = {! ⟦ t ⟧ ts cs   !} --(t [ ts ]) , (s [ ts ]) , β-step β-π₁ β-base , β-step β-π₂ β-base , ⟦ t ⟧ ts cs , ⟦ s ⟧ ts cs
⟦ π₁ t ⟧ ts cs = {!   !}
⟦ π₂ t ⟧ ts cs = {!   !}
⟦ t · t₁ ⟧ ts cs = {!   !}
⟦ ƛ t ⟧ ts cs = {!   !}

-- canonicity   
-- [[]] : (t : [] ⊢ σ) → (t [ [] ]) ≡ t
-- [[]] yes = refl
-- [[]] no = refl
-- [[]] ⟨⟩ = refl
-- [[]] (t , s) = pair-term-≡ ([[]] t) ([[]] s)
-- [[]] (π₁ t) = cong π₁ ([[]] t)
-- [[]] (π₂ t) = cong π₂ ([[]] t)
-- [[]] (ƛ t) = cong ƛ_ subst-idSub
-- [[]] (t · s) = app-term-≡ ([[]] t) ([[]] s)

-- thm[canonicity] : (t : [] ⊢ Ans) → ([] ⊢ t ≐ yes ∶ Ans) ⊎ ([] ⊢ t ≐ no ∶ Ans)
-- thm[canonicity] t with ⟦ t ⟧ [] [] 
-- ... | t' , t[[]]→t' , .yes , t'→yes , inl refl = inl (β-red (β-step (β-refl (≡-sym ([[]] t))) (concatβ* t[[]]→t' t'→yes)))
-- ... | t' , t[[]]→t' , .no , t'→no , inr refl = inr (β-red (β-step (β-refl (≡-sym ([[]] t))) (concatβ* t[[]]→t' t'→no)))

-- test-term : [] ⊢ Ans
-- test-term = (ƛ (` ze)) · (π₁ (π₂ (yes , ((ƛ (` ze)) · no)) , ⟨⟩))

-- test-canonicity : ([] ⊢ test-term ≐ yes ∶ Ans) ⊎ ([] ⊢ test-term ≐ no ∶ Ans)
-- test-canonicity = thm[canonicity] test-term 