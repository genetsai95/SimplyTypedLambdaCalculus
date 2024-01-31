module STLC.Normal where

open import Prelude
open import STLC.Base
open import STLC.TermEquationalReasonings
open import STLC.Renaming
open import STLC.Substitution

-- definition of neutral and normal forms
data Neutral : (Γ : Cxt)(σ : Type) → Γ ⊢ σ → Set
data Normal : (Γ : Cxt)(σ : Type) → Γ ⊢ σ → Set

data Neutral where
    `_ : (x : Γ ∋ σ) → Neutral Γ σ (` x)
    π₁ : {p : Γ ⊢ σ ẋ τ} → Neutral Γ (σ ẋ τ) p → Neutral Γ σ (π₁ p)
    π₂ : {p : Γ ⊢ σ ẋ τ} → Neutral Γ (σ ẋ τ) p → Neutral Γ τ (π₂ p)
    _·_ : {f : Γ ⊢ σ ⇒ τ}{a : Γ ⊢ σ} → Neutral Γ (σ ⇒ τ) f → Normal Γ σ a → Neutral Γ τ (f · a)

data Normal where
    yes : ∀{Γ} → Normal Γ Ans yes
    no : ∀{Γ} → Normal Γ Ans no
    ‘_ : {a : Γ ⊢ Ans} → Neutral Γ Ans a → Normal Γ Ans a
    ⟨⟩ : ∀{Γ} → Normal Γ 𝟙 ⟨⟩
    ‘‘_ : {a : Γ ⊢ 𝟙} → Neutral Γ 𝟙 a → Normal Γ 𝟙 a
    _,_ : {a : Γ ⊢ σ}{b : Γ ⊢ τ} → Normal Γ σ a → Normal Γ τ b → Normal Γ (σ ẋ τ) (a , b)
    ƛ_ : {t : σ ∷ Γ ⊢ τ} → Normal (σ ∷ Γ) τ t → Normal Γ (σ ⇒ τ) (ƛ t)

-- renaming preserves neutral and normal forms
rename-nf : (ρ : Ren Γ Δ){t : Γ ⊢ σ} → Normal Γ σ t → Normal Δ σ (rename ρ t)
rename-ne : (ρ : Ren Γ Δ){t : Γ ⊢ σ} → Neutral Γ σ t → Neutral Δ σ (rename ρ t)

rename-nf ρ yes = yes
rename-nf ρ no = no
rename-nf ρ (‘ x) = ‘ rename-ne ρ x
rename-nf ρ ⟨⟩ = ⟨⟩
rename-nf ρ (‘‘ x) = ‘‘ rename-ne ρ x
rename-nf ρ (n₁ , n₂) = rename-nf ρ n₁ , rename-nf ρ n₂
rename-nf ρ (ƛ n) = ƛ rename-nf (lift ρ) n

rename-ne ρ (` x) = ` lookupRen x ρ
rename-ne ρ (π₁ n) = π₁ (rename-ne ρ n)
rename-ne ρ (π₂ n) = π₂ (rename-ne ρ n)
rename-ne ρ (n · x) = rename-ne ρ n · rename-nf ρ x

-- substitution with neutral terms
data NeutralSub : Sub Γ Δ → Set where
    [] : NeutralSub ([] {Γ})
    _∷_ : {t : Δ ⊢ σ}{ts : Sub Γ Δ} → Neutral Δ σ t → NeutralSub ts → NeutralSub (t ∷ ts)

neutralsub-each : (ts : Sub Γ Δ) → (∀{σ} → (x : Γ ∋ σ) → Neutral Δ σ (lookup x ts)) → NeutralSub ts
neutralsub-each [] ne-each = []
neutralsub-each (t ∷ ts) ne-each = ne-each ze ∷ neutralsub-each ts (λ x → ne-each (su x))

idSub-is-neutral : ∀{Γ} → NeutralSub (idSub {Γ})
idSub-is-neutral {Γ} = neutralsub-each idSub each
    where
        each : ∀{σ} → (x : Γ ∋ σ) → Neutral Γ σ (lookup x idSub)
        each {σ} x = transport (Neutral Γ σ) (≡-sym lookup-idSub) (` x)