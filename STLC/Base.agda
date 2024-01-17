module STLC.Base where

open import Prelude

-- definitions of types and contexts
data Type : Set where
    Ans : Type
    𝟙 : Type
    _ẋ_ : Type → Type → Type
    _⇒_ : Type → Type → Type

infix 30 _ẋ_
infix 30 _⇒_

Cxt = List Type

variable
    Γ Δ Θ : Cxt
    σ τ φ ψ : Type


-- definitions of terms
data _∋_ : Cxt → Type → Set where
    ze : σ ∷ Γ ∋ σ
    su : Γ ∋ σ → τ ∷ Γ ∋ σ

data _⊢_ : Cxt → Type → Set where
    `_ : Γ ∋ σ → Γ ⊢ σ
    yes : Γ ⊢ Ans
    no : Γ ⊢ Ans
    ⟨⟩ : Γ ⊢ 𝟙
    _,_ : Γ ⊢ σ → Γ ⊢ τ → Γ ⊢ σ ẋ τ
    π₁ : Γ ⊢ σ ẋ τ → Γ ⊢ σ
    π₂ : Γ ⊢ σ ẋ τ → Γ ⊢ τ
    _·_ : Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ
    ƛ_ : σ ∷ Γ ⊢ τ → Γ ⊢ (σ ⇒ τ)

infix 25 _⊢_
infix 30 _·_ 