module STLC.Substitution where

open import Prelude
open import STLC.Base
open import STLC.Renaming
open import STLC.TermEquationalReasonings

-- definitions about substitution

data Sub : Cxt → Cxt → Set where
    [] : Sub [] Δ
    _∷_ : Δ ⊢ σ → Sub Γ Δ → Sub (σ ∷ Γ) Δ

mapSub : (∀{σ} → Δ ⊢ σ → Θ ⊢ σ) → Sub Γ Δ → Sub Γ Θ
mapSub _ [] = []
mapSub f (t ∷ ts) = f t ∷ mapSub f ts

lookup : Γ ∋ σ → Sub Γ Δ → Δ ⊢ σ
lookup ze (t ∷ _) = t
lookup (su n) (_ ∷ ts) = lookup n ts

_↑ : Sub Γ Δ → Sub (σ ∷ Γ) (σ ∷ Δ)
ts ↑ = (` ze) ∷ mapSub weaken ts

subst : Γ ⊢ σ → Sub Γ Δ → Δ ⊢ σ
subst (` x) ts = lookup x ts
subst yes ts = yes
subst no ts = no
subst ⟨⟩ ts = ⟨⟩
subst (t₁ , t₂) ts = subst t₁ ts , subst t₂ ts
subst (π₁ t) ts = π₁ (subst t ts)
subst (π₂ t) ts = π₂ (subst t ts)
subst (ƛ t) ts = ƛ subst t (ts ↑)
subst (t · t') ts = subst t ts · subst t' ts

_⊙_ : Sub Γ Δ → Sub Δ Θ → Sub Γ Θ
ts ⊙ ss = mapSub (λ t → subst t ss) ts

idSub : ∀{Γ} → Sub Γ Γ
idSub {[]} = []
idSub {t ∷ Γ} = idSub ↑

_[_/x] : σ ∷ Γ ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
t [ s /x] = subst t (s ∷ idSub)

infix 30 _[_/x]

rename-to-sub : Γ ⊆ Δ → Sub Γ Δ
rename-to-sub {[]} ρ = []
rename-to-sub {σ ∷ Γ} ρ = (` ρ ze) ∷ rename-to-sub (pop ρ)

-- equalities about substitution

∷-sub-eq : {Γ Δ : Cxt}{σ : Type} → {t s : Δ ⊢ σ}{ts ss : Sub Γ Δ} → t ≡ s → ts ≡ ss → _≡_ {X = Sub (σ ∷ Γ) Δ}(t ∷ ts) (s ∷ ss)
∷-sub-eq refl refl = refl

sub-head-eq-elim : ∀{σ} → {ts ss : Sub Γ Δ}{t : Δ ⊢ σ} → _≡_ {X = Sub (σ ∷ Γ) Δ} (t ∷ ts) (t ∷ ss) → ts ≡ ss
sub-head-eq-elim refl = refl

mapSub-fusion : ∀{Γ Δ Δ' Δ''} → (f : ∀{σ} → Δ' ⊢ σ → Δ'' ⊢ σ)(g : ∀{σ} → Δ ⊢ σ → Δ' ⊢ σ){ts : Sub Γ Δ} → (mapSub {Γ = Γ} f ∘ mapSub g) ts ≡ mapSub (f ∘ g) ts
mapSub-fusion f g {[]} = refl
mapSub-fusion f g {t ∷ ts} = mapSub f (mapSub g (t ∷ ts))
                           ≡⟨ refl ⟩ mapSub f (g t ∷ mapSub g ts)
                           ≡⟨ refl ⟩ f (g t) ∷ mapSub f (mapSub g ts)
                           ≡⟨ cong (f (g t) ∷_) (mapSub-fusion f g {ts}) ⟩ f (g t) ∷ mapSub (f ∘ g) ts
                           ≡⟨ refl ⟩ (f ∘ g) t ∷ mapSub (f ∘ g) ts
                           ≡⟨ refl ⟩ mapSub (f ∘ g) (t ∷ ts) ∎

eqSub : (ts ss : Sub Γ Δ) → (∀{σ} → (n : Γ ∋ σ) → lookup n ts ≡ lookup n ss) → ts ≡ ss
eqSub [] [] _ = refl
eqSub (t ∷ ts) (s ∷ ss) eq with eq ze
... | refl = cong (t ∷_) (eqSub ts ss λ n → eq (su n))

lookup-map : (f : ∀{τ} → Δ ⊢ τ → Θ ⊢ τ){ts : Sub Γ Δ}(x : Γ ∋ σ){t : Δ ⊢ σ} → lookup x ts ≡ t → lookup x (mapSub f ts) ≡ f t
lookup-map f {ts = t ∷ ts} ze refl = refl
lookup-map f {ts = t ∷ ts} (su x) refl = lookup-map f {ts = ts} x refl

lookup-idSub : {x : Γ ∋ σ} → lookup x idSub ≡ (` x)
lookup-idSub {x = ze} = refl
lookup-idSub {Γ = σ ∷ Γ} {x = su x} = 
                                      lookup x (mapSub weaken idSub)
                                    ≡⟨ lookup-map weaken {ts = idSub} x (lookup-idSub {x = x}) ⟩ 
                                      weaken (` x)
                                    ≡⟨ weaken≡weaken' (` x) ⟩
                                      weaken' (` x)
                                    ≡⟨ refl ⟩
                                      (` su x)
                                    ∎

lookup-su : ∀{τ τ'} → (x : Γ ∋ σ)(t : Δ ⊢ τ)(s : Δ ⊢ τ')(ts : Sub Γ Δ) → lookup (su x) (t ∷ ts) ≡ lookup (su x) (s ∷ ts)
lookup-su x t s ts = refl

subst-idSub : {t : Γ ⊢ σ} → subst t idSub ≡ t
subst-idSub {t = ` x} = lookup-idSub
subst-idSub {t = yes} = refl
subst-idSub {t = no} = refl
subst-idSub {t = ⟨⟩} = refl
subst-idSub {t = t , s} = pair-term-≡ subst-idSub subst-idSub
subst-idSub {t = π₁ t} = cong π₁ subst-idSub
subst-idSub {t = π₂ t} = cong π₂ subst-idSub
subst-idSub {t = ƛ t} = cong ƛ_ subst-idSub
subst-idSub {t = t · s} = app-term-≡ subst-idSub subst-idSub

lookup-⊙ : ∀{σ} → {ts : Sub Γ Δ}{ss : Sub Δ Θ}(x : Γ ∋ σ) → lookup x (ts ⊙ ss) ≡ subst (lookup x ts) ss
lookup-⊙ {ss = ss} x = lookup-map (λ t → subst t ss) x refl