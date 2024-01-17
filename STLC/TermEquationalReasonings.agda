module STLC.TermEquationalReasonings where

open import Prelude
open import STLC.Base

pair-term-≡ : {t₁ t₂ : Γ ⊢ σ}{s₁ s₂ : Γ ⊢ τ} → t₁ ≡ t₂ → s₁ ≡ s₂ → _⊢_._,_ t₁ s₁ ≡ _⊢_._,_ t₂ s₂
pair-term-≡ refl refl = refl

app-term-≡ : {t₁ t₂ : Γ ⊢ σ ⇒ τ}{s₁ s₂ : Γ ⊢ σ} → t₁ ≡ t₂ → s₁ ≡ s₂ → (t₁ · s₁) ≡ (t₂ · s₂)
app-term-≡ refl refl = refl

`-elim-≡ : {x y : Γ ∋ σ} → (` x) ≡ (` y) → x ≡ y
`-elim-≡ refl = refl