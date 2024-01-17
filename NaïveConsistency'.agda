module NaïveConsistency' where

open import Prelude
open import STLC

-- interpretation of types
⟦_⟧ᵗ : Type → Set
⟦ Ans ⟧ᵗ = 𝟚
⟦ 𝟙 ⟧ᵗ = ⊤
⟦ σ ẋ τ ⟧ᵗ = ⟦ σ ⟧ᵗ × ⟦ τ ⟧ᵗ
⟦ σ ⇒ τ ⟧ᵗ = ⟦ σ ⟧ᵗ → ⟦ τ ⟧ᵗ

-- interpretation of contexts
data ⟦_⟧ᶜ : Cxt → Set where
    [] : ⟦ [] ⟧ᶜ
    _∷_ : ⟦ σ ⟧ᵗ → ⟦ Γ ⟧ᶜ → ⟦ σ ∷ Γ ⟧ᶜ

lookupCxt : Γ ∋ σ → ⟦ Γ ⟧ᶜ → ⟦ σ ⟧ᵗ
lookupCxt ze (t ∷ _) = t
lookupCxt (su n) (_ ∷ ts) = lookupCxt n ts


-- interpretation of terms
⟦_⟧ : Γ ⊢ σ → ⟦ Γ ⟧ᶜ → ⟦ σ ⟧ᵗ
⟦ ` x ⟧ ts = lookupCxt x ts
⟦ yes ⟧ ts = `t
⟦ no ⟧ ts = `f
⟦ ⟨⟩ ⟧ ts = `nil
⟦ t , s ⟧ ts = ⟦ t ⟧ ts , ⟦ s ⟧ ts
⟦ π₁ t ⟧ = pr₁ ∘ ⟦ t ⟧
⟦ π₂ t ⟧ = pr₂ ∘ ⟦ t ⟧
⟦ ƛ t ⟧ ts = λ u → ⟦ t ⟧ (u ∷ ts)
⟦ t · s ⟧ ts = ⟦ t ⟧ ts (⟦ s ⟧ ts)

postulate
    extensionality : {X : Set}{Y : X → Set}(f g : (x : X) → Y x) → ((x : X) → f x ≡ g x) → f ≡ g

lem[interpret-subst] : {t : τ ∷ Γ ⊢ σ}{s : Γ ⊢ τ}{ts : ⟦ Γ ⟧ᶜ} → ⟦ subst t (s ∷ idSub) ⟧ ts ≡ ⟦ t ⟧ (⟦ s ⟧ ts ∷ ts)
lem[interpret-subst] {t = ` ze} = refl
lem[interpret-subst] {t = ` su x} {s = s} {ts = ts} = 
                                                        ⟦ lookup x idSub ⟧ ts
                                                    ≡⟨ cong (λ t' → ⟦ t' ⟧ ts) (lookup-idSub {x = x}) ⟩ 
                                                        ⟦ (` x) ⟧ ts
                                                    ≡⟨ refl ⟩
                                                        lookupCxt x ts
                                                    ∎
lem[interpret-subst] {t = yes} = refl
lem[interpret-subst] {t = no} = refl
lem[interpret-subst] {t = ⟨⟩} = refl
lem[interpret-subst] {t = t , t'} = pair-≡ (lem[interpret-subst] {t = t}) (lem[interpret-subst] {t = t'})
lem[interpret-subst] {t = π₁ t} = cong pr₁ (lem[interpret-subst] {t = t})
lem[interpret-subst] {t = π₂ t} = cong pr₂ (lem[interpret-subst] {t = t})
lem[interpret-subst] {t = t · t'} = app-≡ (lem[interpret-subst] {t = t}) (lem[interpret-subst] {t = t'})
lem[interpret-subst] {τ = τ} {σ = σ} {t = ƛ_ {σ = σ'} t} {s = s} {ts = ts} = 
      ⟦ ƛ subst t ((` ze) ∷ mapSub weaken (s ∷ idSub)) ⟧ ts
    ≡⟨ extensionality (⟦ ƛ subst t ((` ze) ∷ mapSub weaken (s ∷ idSub)) ⟧ ts) {!   !} (λ u → {!   !}) ⟩ {!   !}
    where
        -- eqt : subst t (s ∷ idSub) ≡ subst (subst t idSub) (s ∷ idSub)
        -- eqt = ?
        
        eqf : ∀ u → ⟦ ƛ subst t ((` ze) ∷ mapSub weaken (s ∷ idSub)) ⟧ ts u ≡ ⟦ t ⟧ (u ∷ (⟦ s ⟧ ts ∷ ts))
        eqf u = {!   !}

⟦β→⟧ : {a b : Γ ⊢ σ} → a →β b → ⟦ a ⟧ =f= ⟦ b ⟧
⟦β→⟧ (β-refl refl) u = refl
⟦β→⟧ (β-ƛ {t = t} {s = s}) u = ≡-sym (  ⟦ subst t (s ∷ idSub) ⟧ u
                                    ≡⟨ lem[interpret-subst] {t = t} {s = s} ⟩
                                       ⟦ t ⟧ (⟦ s ⟧ u ∷ u) 
                                    ∎)
⟦β→⟧ β-π₁ u = refl
⟦β→⟧ β-π₂ u = refl
⟦β→⟧ (ξ-app t→t' s→s') u = app-≡ (⟦β→⟧ t→t' u) (⟦β→⟧ s→s' u)
⟦β→⟧ (ξ-pair t→t' s→s') u = pair-≡ (⟦β→⟧ t→t' u) (⟦β→⟧ s→s' u)
⟦β→⟧ (ξ-π₁ t→t') u = cong pr₁ (⟦β→⟧ t→t' u)
⟦β→⟧ (ξ-π₂ t→t') u = cong pr₂ (⟦β→⟧ t→t' u)

⟦β→*⟧ : {a b : Γ ⊢ σ} → a →β* b → ⟦ a ⟧ =f= ⟦ b ⟧
⟦β→*⟧ β-base u = refl
⟦β→*⟧ (β-step r rs) u = ftrans (⟦β→⟧ r) (⟦β→*⟧ rs) u

thm[consistency] : {a b : Γ ⊢ σ} → Γ ⊢ a ≐ b ∶ σ → ⟦ a ⟧ =f= ⟦ b ⟧
thm[consistency] reflⱼ u = refl
thm[consistency] (β-red rs) = ⟦β→*⟧ rs

`t≢`f : `t ≡ `f → ⊥
`t≢`f ()

inst-of-cxt : (Γ : Cxt) → ⟦ Γ ⟧ᶜ
inst-of-cxt [] = []
inst-of-cxt (Ans ∷ Γ) = `t ∷ inst-of-cxt Γ
inst-of-cxt (𝟙 ∷ Γ) = `nil ∷ inst-of-cxt Γ
inst-of-cxt ((σ ẋ τ) ∷ Γ) with inst-of-cxt (σ ∷ []) | inst-of-cxt (τ ∷ [])
... | s ∷ _ | t ∷ _ = (s , t) ∷ inst-of-cxt Γ
inst-of-cxt ((σ ⇒ τ) ∷ Γ) with inst-of-cxt (τ ∷ [])
... | t ∷ _ = (λ _ → t) ∷ inst-of-cxt Γ
 
thm[eq-consistency] : Γ ⊢ yes ≐ no ∶ Ans → ⊥
thm[eq-consistency] {Γ} eq = `t≢`f (thm[consistency] eq (inst-of-cxt Γ)) 