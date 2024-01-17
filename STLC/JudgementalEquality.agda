module STLC.JudgementalEquality where

open import STLC.Base
open import STLC.Reduction

data JEq (Γ : Cxt)(σ : Type) : Γ ⊢ σ → Γ ⊢ σ → Set where
    reflⱼ : {a : Γ ⊢ σ} → JEq Γ σ a a
    β-red : {a b : Γ ⊢ σ} → a →β* b → JEq Γ σ a b
    -- symⱼ : {a b : Γ ⊢ σ} → JEq Γ σ a b → JEq Γ σ b a
    -- transⱼ : {a b c : Γ ⊢ σ} → JEq Γ σ a b → JEq Γ σ b c → JEq Γ σ a c
  
syntax JEq Γ σ a b = Γ ⊢ a ≐ b ∶ σ