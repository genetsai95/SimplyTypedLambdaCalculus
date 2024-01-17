module STLC-old where

open import Prelude

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
    ƛ_ : σ ∷ Γ ⊢ τ → Γ ⊢ (σ ⇒ τ)
    _·_ : Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ

infix 25 _⊢_
infix 30 _·_ 

type-of-term : Γ ⊢ σ → Type
type-of-term {σ = σ} _ = σ

-- renaming
_⊆_ : Cxt → Cxt → Set
Γ ⊆ Δ = ∀{σ} → Γ ∋ σ → Δ ∋ σ

concat⊆ : Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
concat⊆ s₁ s₂ x = s₂ (s₁ x)

ext : Γ ⊆ Δ → σ ∷ Γ ⊆ σ ∷ Δ
ext ρ ze = ze
ext ρ (su x) = su (ρ x)

_⊨_ : Cxt → Cxt → Set
Γ ⊨ Δ = ∀{σ} → Γ ⊢ σ → Δ ⊢ σ

rename : Γ ⊆ Δ → Γ ⊨ Δ
rename ρ (` x) = ` (ρ x)
rename ρ yes = yes
rename ρ no = no
rename ρ ⟨⟩ = ⟨⟩
rename ρ (t , s) = rename ρ t , rename ρ s
rename ρ (π₁ t) = π₁ (rename ρ t)
rename ρ (π₂ t) = π₂ (rename ρ t)
rename ρ (t · s) = rename ρ t · rename ρ s
rename ρ (ƛ t) = ƛ rename (ext ρ) t

-- weakening
weaken : Γ ⊨ (σ ∷ Γ)
weaken = rename su

-- substitution
_⊩_ : Cxt → Cxt → Set
Γ ⊩ Δ = ∀{σ} → Γ ∋ σ → Δ ⊢ σ

exts : Γ ⊩ Δ → σ ∷ Γ ⊩ σ ∷ Δ
exts ρ ze = ` ze
exts ρ (su x) = rename su (ρ x) -- weaken (ρ x)

subst : Γ ⊩ Δ → Γ ⊨ Δ
subst ρ (` x) = ρ x
subst ρ yes = yes
subst ρ no = no
subst ρ ⟨⟩ = ⟨⟩
subst ρ (t , s) = subst ρ t , subst ρ s
subst ρ (π₁ t) = π₁ (subst ρ t)
subst ρ (π₂ t) = π₂ (subst ρ t)
subst ρ (t · s) = subst ρ t · subst ρ s
subst ρ (ƛ t) = ƛ subst (exts ρ) t

ext-by-term : Γ ⊩ Δ → Δ ⊢ σ → (σ ∷ Γ) ⊩ Δ
ext-by-term ρ t ze = t
ext-by-term ρ t (su x) = ρ x

_[_/x] : σ ∷ Γ ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
t [ s /x] = subst (ext-by-term `_ s) t

infix 30 _[_/x]

-- term equality
pair-term-≡ : {t₁ t₂ : Γ ⊢ σ}{s₁ s₂ : Γ ⊢ τ} → t₁ ≡ t₂ → s₁ ≡ s₂ → _⊢_._,_ t₁ s₁ ≡ _⊢_._,_ t₂ s₂
pair-term-≡ refl refl = refl

app-term-≡ : {t₁ t₂ : Γ ⊢ σ ⇒ τ}{s₁ s₂ : Γ ⊢ σ} → t₁ ≡ t₂ → s₁ ≡ s₂ → (t₁ · s₁) ≡ (t₂ · s₂)
app-term-≡ refl refl = refl

-- judgemental equality
data JEq (Γ : Cxt)(σ : Type) : Γ ⊢ σ → Γ ⊢ σ → Set where
    reflⱼ : {a : Γ ⊢ σ} → JEq Γ σ a a
    symⱼ : {a b : Γ ⊢ σ} → JEq Γ σ a b → JEq Γ σ b a
    transⱼ : {a b c : Γ ⊢ σ} → JEq Γ σ a b → JEq Γ σ b c → JEq Γ σ a c
    β-π₁ : {a : Γ ⊢ σ}{b : Γ ⊢ τ} → JEq Γ σ (π₁ (a , b)) a
    β-π₂ : {a : Γ ⊢ τ}{b : Γ ⊢ σ} → JEq Γ σ (π₂ (a , b)) b
    β-ƛ : {t : τ ∷ Γ ⊢ σ}{s : Γ ⊢ τ} → JEq Γ σ ((ƛ t) · s) (t [ s /x])

syntax JEq Γ σ a b = Γ ⊢ a ≐ b ∶ σ



-- reduction
-- data _→β_ : Γ ⊢ σ → Γ ⊢ σ → Set where
--     β-ƛ : {t : σ ∷ Γ ⊢ τ}{s : Γ ⊢ σ} → (ƛ t) · s →β t [ s /x]
--     β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₁ (t , s) →β t
--     β-π₂ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → π₂ (t , s) →β s

-- data _→β*_ : Γ ⊢ σ → Γ ⊢ σ → Set where
--     β-base : (t : Γ ⊢ σ) → t →β* t
--     β-step : {t u v : Γ ⊢ σ} → t →β* u → u →β v → t →β* v

-- [_]β : (t : Γ ⊢ σ) → Set
-- [_]β {Γ} {σ} t = ∃[ t' ∶ Γ ⊢ σ ] (∃[ t'' ∶ Γ ⊢ σ ] ((t →β* t'') × (t' →β* t'')))

