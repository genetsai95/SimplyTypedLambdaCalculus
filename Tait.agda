module Tait where

open import Prelude
open import STLC

module STLC_Naïve_canonicity where

    -- context -> list of closed terms with corresponding types
    ⟦_⟧ᶜ : Cxt → Set
    ⟦ [] ⟧ᶜ = ⊤
    ⟦ σ ∷ Γ ⟧ᶜ = ([] ⊢ σ) × ⟦ Γ ⟧ᶜ

    -- closed term substitution
    closed-terms : ⟦ Γ ⟧ᶜ → Γ ⊩ []
    closed-terms {[]} `nil ()
    closed-terms {σ ∷ Γ} (a , _) ze = a
    closed-terms {σ ∷ Γ} (_ , as) (su x) = closed-terms as x

    -- _[_] :  Γ ⊢ σ → ⟦ Γ ⟧ᶜ → [] ⊢ σ
    -- t [ a ] = subst (closed-terms a) t

    _[_] :  Γ ⊢ σ → ⟦ Γ ⟧ᶜ → [] ⊢ σ
    (` ze) [ a , _ ] = a
    (` su x) [ _ , as ] = (` x) [ as ]
    yes [ a ] = yes
    no [ a ] = no
    ⟨⟩ [ a ] = ⟨⟩
    (t , s) [ a ] = (t [ a ]) , (s [ a ])
    π₁ t [ a ] = π₁ (t [ a ])
    π₂ t [ a ] = π₂ (t [ a ])
    (t · s) [ a ] = (t [ a ]) · (s [ a ])
    (ƛ t) [ a ] = ƛ subst (exts (closed-terms a)) t

    -- test : [] ⊢ 𝟙 ẋ (Ans ⇒ 𝟙)
    -- test = ((` ze) , (ƛ (` (su ze)))) [ ⟨⟩ , `nil ]

    -- computability structure
    Comp : (σ : Type) → [] ⊢ σ → Set
    Comp (σ ẋ τ) t = Comp σ (π₁ t) × Comp τ (π₂ t)
    Comp 𝟙 t = ⊤
    Comp (σ ⇒ τ) t = (a : [] ⊢ σ)(u : Comp σ a) → Comp τ (t · a)
    Comp Ans t = Σ 𝟚 (λ{`t → ([] ⊢ t ≐ yes ∶ Ans); `f → ([] ⊢ t ≐ no ∶ Ans)})

    comp-β-π₁ : {t : [] ⊢ σ}{s : [] ⊢ τ} → Comp σ t → Comp σ (π₁ (t , s))
    comp-β-π₁ {σ = Ans} {s = s} (`t , eq) = `t , transⱼ β-π₁ eq
    comp-β-π₁ {σ = Ans} {s = s} (`f , eq) = `f , transⱼ β-π₁ eq
    comp-β-π₁ {σ = 𝟙} {s = s} u = `nil
    comp-β-π₁ {σ = σ ẋ τ} {s = s} (u , v) = {! comp-β-π₁ u  !}
    comp-β-π₁ {σ = σ ⇒ τ} {s = s} u = {!   !}

    -- -- context -> corresponding computability structures for closed terms
    -- ⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ → Set
    -- ⟦ [] ⟧ˢ `nil = ⊤
    -- ⟦ σ ∷ Γ ⟧ˢ (a , as) = Comp σ a × ⟦ Γ ⟧ˢ as

    -- -- computability morphism
    -- ⟦_⟧ : (t : Γ ⊢ σ) → (a : ⟦ Γ ⟧ᶜ)(u : ⟦ Γ ⟧ˢ a) → Comp σ (t [ a ])
    -- ⟦ ` ze ⟧ (a , _) (u , _) = u
    -- ⟦ ` su x ⟧ (_ , as) (_ , us) = ⟦ ` x ⟧ as us
    -- ⟦ yes ⟧ a u = {!   !} --`t , refl
    -- ⟦ no ⟧ a u = {!   !} --`f , refl
    -- ⟦ ⟨⟩ ⟧ a u = `nil
    -- ⟦ π₁ t ⟧ a u = pr₁ (⟦ t ⟧ a u)
    -- ⟦ π₂ t ⟧ a u = pr₂ (⟦ t ⟧ a u)
    -- ⟦ t , s ⟧ a u = {! ⟦ t ⟧ a u  !} --⟦ t ⟧ a u , ⟦ s ⟧ a u
    -- ⟦ t · s ⟧ a u = ⟦ t ⟧ a u (s [ a ]) (⟦ s ⟧ a u)
    -- ⟦ ƛ t ⟧ a u = {!   !} -- λ a' u' → ⟦ t ⟧ (a' , a) (u' , u)

    -- -- canonicity
    -- thm[canonicity] : (t : [] ⊢ Ans) → (t ≡ yes) ⊎ (t ≡ no)
    -- thm[canonicity] t with ⟦ t ⟧ `nil `nil
    -- ... | `t , eq = inl {!  !} 
    -- ... | `f , eq = inr {!   !}

open STLC_Naïve_canonicity public