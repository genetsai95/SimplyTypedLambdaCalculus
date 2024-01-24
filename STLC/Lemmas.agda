module STLC.Lemmas where

open import Prelude
open import STLC.Base
open import STLC.TermEquationalReasonings
open import STLC.Renaming
open import STLC.Substitution

lookup-lookupRen-su-↑ : ∀{τ} → (x : Γ ∋ σ)(ρ : Ren Γ Δ)(ts : Sub Δ Θ) → lookup (lookupRen x (mapRen (su {τ = τ}) ρ)) (ts ↑) ≡ weaken (lookup (lookupRen x ρ) ts)
lookup-lookupRen-su-↑ ze (x ∷ ρ) ts = lookup-map weaken x refl
lookup-lookupRen-su-↑ (su x) (_ ∷ ρ) ts = lookup-lookupRen-su-↑ x ρ ts

lookup-wk : ∀{τ τ'} → (x : Γ ∋ σ)(t : Δ ⊢ τ)(s : Δ ⊢ τ')(ts : Sub Γ Δ) → lookup (lookupRen x wk) (t ∷ ts) ≡ lookup (lookupRen x wk) (s ∷ ts)
lookup-wk x t s ts = lookup (lookupRen x wk) (t ∷ ts)
                   ≡⟨ cong (λ y → lookup y (t ∷ ts)) (lookupRen-wk x) ⟩ lookup (su x) (t ∷ ts)
                   ≡⟨ lookup-su x t s ts ⟩ lookup (su x) (s ∷ ts)
                   ≡⟨ ≡-sym (cong (λ y → lookup y (s ∷ ts)) (lookupRen-wk x)) ⟩ lookup (lookupRen x wk) (s ∷ ts) ∎

sr-sr-eq : ∀{Δ Δ'} → {ρ : Ren Γ Δ}{ρ' : Ren Γ Δ'}{ts : Sub Δ Θ}{ss : Sub Δ' Θ}
         → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ subst (rename ρ' (` x)) ss)
         → {σ : Type}(t : Γ ⊢ σ) → subst (rename ρ t) ts ≡ subst (rename ρ' t) ss
sr-sr-eq eqv (` x) = eqv x
sr-sr-eq eqv yes = refl
sr-sr-eq eqv no = refl
sr-sr-eq eqv ⟨⟩ = refl
sr-sr-eq eqv (t , s) = pair-term-≡ (sr-sr-eq eqv t) (sr-sr-eq eqv s)
sr-sr-eq eqv (π₁ t) = cong π₁ (sr-sr-eq eqv t)
sr-sr-eq eqv (π₂ t) = cong π₂ (sr-sr-eq eqv t)
sr-sr-eq eqv (t · s) = app-term-≡ (sr-sr-eq eqv t) (sr-sr-eq eqv s)
sr-sr-eq eqv (ƛ t) = cong ƛ_ (sr-sr-eq (eq-lift eqv) t)
    where
        eq-lift : ∀{Δ Δ'} → {ρ : Ren Γ Δ}{ρ' : Ren Γ Δ'}{ts : Sub Δ Θ}{ss : Sub Δ' Θ}
                → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ subst (rename ρ' (` x)) ss)
                → {σ τ : Type} → (x : τ ∷ Γ ∋ σ) → subst (rename (lift ρ) (` x)) (ts ↑) ≡ subst (rename (lift ρ') (` x)) (ss ↑)
        eq-lift eqv ze = refl
        eq-lift {ρ = ρ} {ρ' = ρ'} {ts = ts} {ss = ss} eqv (su x) = lookup (lookupRen x (mapRen su ρ)) (ts ↑)
                                                                 ≡⟨ lookup-lookupRen-su-↑ x ρ ts ⟩ weaken (lookup (lookupRen x ρ) ts)
                                                                 ≡⟨ cong weaken (eqv x) ⟩ weaken (lookup (lookupRen x ρ') ss)
                                                                 ≡⟨ ≡-sym (lookup-lookupRen-su-↑ x ρ' ss) ⟩ lookup (lookupRen x (mapRen su ρ')) (ss ↑) ∎

sr-r-eq : {ρ : Ren Γ Δ}{ts : Sub Δ Θ}{ρ' : Ren Γ Θ}
          → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ (rename ρ' (` x)))
          → {σ : Type}(t : Γ ⊢ σ) → subst (rename ρ t) ts ≡ rename ρ' t
sr-r-eq eqv (` x) = eqv x
sr-r-eq eqv yes = refl
sr-r-eq eqv no = refl
sr-r-eq eqv ⟨⟩ = refl
sr-r-eq eqv (t , s) = pair-term-≡ (sr-r-eq eqv t) (sr-r-eq eqv s)
sr-r-eq eqv (π₁ t) = cong π₁ (sr-r-eq eqv t)
sr-r-eq eqv (π₂ t) = cong π₂ (sr-r-eq eqv t)
sr-r-eq eqv (t · s) = app-term-≡ (sr-r-eq eqv t) (sr-r-eq eqv s)
sr-r-eq eqv (ƛ t) = cong ƛ_ (sr-r-eq (eq-lift eqv) t)
    where
        eq-lift : {ρ : Ren Γ Δ}{ts : Sub Δ Θ}{ρ' : Ren Γ Θ}
                → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ (rename ρ' (` x)))
                → {σ τ : Type}(x : τ ∷ Γ ∋ σ) → subst (rename (lift ρ) (` x)) (ts ↑) ≡ rename (lift ρ') (` x)
        eq-lift eqv ze = refl
        eq-lift {ρ = ρ} {ts = ts} {ρ' = ρ'} eqv (su x) = lookup (lookupRen x (mapRen su ρ)) (ts ↑)
                                                       ≡⟨ cong (λ y → lookup y (ts ↑)) (lookupRen-map su x refl) ⟩ lookup (lookupRen x ρ) (mapSub weaken ts)
                                                       ≡⟨ lookup-map weaken (lookupRen x ρ) refl ⟩ weaken (lookup (lookupRen x ρ) ts)
                                                       ≡⟨ cong weaken (eqv x) ⟩ weaken (` lookupRen x ρ')
                                                       ≡⟨ refl ⟩ (` lookupRen (lookupRen x ρ') (mapRen su idRen))
                                                       ≡⟨ cong `_ (lookupRen-wk (lookupRen x ρ')) ⟩ (` su (lookupRen x ρ'))
                                                       ≡⟨ cong `_ (≡-sym (lookupRen-map su x refl)) ⟩ (` lookupRen x (mapRen su ρ')) ∎

sr-s-eq : {ρ : Ren Γ Δ}{ts : Sub Δ Θ}{ss : Sub Γ Θ}
          → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ subst (` x) ss)
          → {σ : Type}(t : Γ ⊢ σ) → subst (rename ρ t) ts ≡ subst t ss
sr-s-eq eqv (` x) = eqv x
sr-s-eq eqv yes = refl
sr-s-eq eqv no = refl
sr-s-eq eqv ⟨⟩ = refl
sr-s-eq eqv (t , s) = pair-term-≡ (sr-s-eq eqv t) (sr-s-eq eqv s)
sr-s-eq eqv (π₁ t) = cong π₁ (sr-s-eq eqv t)
sr-s-eq eqv (π₂ t) = cong π₂ (sr-s-eq eqv t)
sr-s-eq eqv (t · s) = app-term-≡ (sr-s-eq eqv t) (sr-s-eq eqv s)
sr-s-eq eqv (ƛ t) = cong ƛ_ (sr-s-eq (eq-lift eqv) t)
  where
    eq-lift : {ρ : Ren Γ Δ}{ts : Sub Δ Θ}{ss : Sub Γ Θ}
              → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ subst (` x) ss)
              → {σ τ : Type}(x : τ ∷ Γ ∋ σ) → subst (rename (lift ρ) (` x)) (ts ↑) ≡ subst (` x) (ss ↑)
    eq-lift {ρ = ρ} {ts} {ss} eqv ze = refl
    eq-lift {ρ = ρ} {ts} {ss} eqv (su x) = lookup (lookupRen x (mapRen su ρ)) (ts ↑)
                                         ≡⟨ cong (λ y → lookup y (ts ↑)) (lookupRen-map su x refl) ⟩ 
                                           lookup (lookupRen x ρ) (mapSub weaken ts) 
                                         ≡⟨ lookup-map weaken (lookupRen x ρ) refl ⟩ 
                                           weaken (lookup (lookupRen x ρ) ts)
                                         ≡⟨ cong weaken (eqv x) ⟩ 
                                           weaken (subst (` x) ss) 
                                         ≡⟨ ≡-sym (lookup-map weaken x refl) ⟩ 
                                           lookup x (mapSub weaken ss)
                                         ∎

rr-eq : ∀{Δ Δ'} → {rs : Ren Γ Δ}{rs' : Ren Γ Δ'}{ss : Ren Δ Θ}{ss' : Ren Δ' Θ}
        → (∀{σ} → (x : Γ ∋ σ) → rename ss (rename rs (` x)) ≡ rename ss' (rename rs' (` x)))
        → {σ : Type}(t : Γ ⊢ σ) → rename ss (rename rs t) ≡ rename ss' (rename rs' t)
rr-eq eqv (` x) = eqv x
rr-eq eqv yes = refl
rr-eq eqv no = refl
rr-eq eqv ⟨⟩ = refl
rr-eq eqv (t , s) = pair-term-≡ (rr-eq eqv t) (rr-eq eqv s)
rr-eq eqv (π₁ t) = cong π₁ (rr-eq eqv t)
rr-eq eqv (π₂ t) = cong π₂ (rr-eq eqv t)
rr-eq eqv (t · s) = app-term-≡ (rr-eq eqv t) (rr-eq eqv s)
rr-eq eqv (ƛ t) = cong ƛ_ (rr-eq (eq-lift eqv) t)
    where
        eq-lift : ∀{Δ Δ'} → {rs : Ren Γ Δ}{rs' : Ren Γ Δ'}{ss : Ren Δ Θ}{ss' : Ren Δ' Θ}
                → (∀{σ} → (x : Γ ∋ σ) → rename ss (rename rs (` x)) ≡ rename ss' (rename rs' (` x)))
                → {σ τ : Type}(x : τ ∷ Γ ∋ σ) → rename (lift ss) (rename (lift rs) (` x)) ≡ rename (lift ss') (rename (lift rs') (` x))
        eq-lift eqv ze = refl
        eq-lift {rs = rs} {rs'} {ss} {ss'} eqv (su x) = (` lookupRen (lookupRen x (mapRen su rs)) (lift ss))
                                                      ≡⟨ cong `_ (cong (λ y → lookupRen y (lift ss)) (lookupRen-map su x refl)) ⟩ (` lookupRen (lookupRen x rs) (mapRen su ss))
                                                      ≡⟨ cong `_ (lookupRen-map su (lookupRen x rs) refl) ⟩ (` su (lookupRen (lookupRen x rs) ss))
                                                      ≡⟨ cong (λ y → ` su y) (`-elim-≡ (eqv x)) ⟩ (` su (lookupRen (lookupRen x rs') ss'))
                                                      ≡⟨ cong `_ (≡-sym (lookupRen-map su (lookupRen x rs') refl)) ⟩ (` lookupRen (lookupRen x rs') (mapRen su ss'))
                                                      ≡⟨ cong `_ (≡-sym (cong (λ y → lookupRen y (lift ss')) (lookupRen-map su x refl))) ⟩ (` lookupRen (lookupRen x (mapRen su rs')) (lift ss')) ∎

rr-r-eq : ∀{Δ} → {rs : Ren Γ Δ}{rs' : Ren Δ Θ}{ss : Ren Γ Θ}
        → (∀{σ} → (x : Γ ∋ σ) → rename rs' (rename rs (` x)) ≡ rename ss (` x))
        → {σ : Type}(t : Γ ⊢ σ) → rename rs' (rename rs t) ≡ rename ss t
rr-r-eq eqv (` x) = eqv x
rr-r-eq eqv yes = refl
rr-r-eq eqv no = refl
rr-r-eq eqv ⟨⟩ = refl
rr-r-eq eqv (t , s) = pair-term-≡ (rr-r-eq eqv t) (rr-r-eq eqv s)
rr-r-eq eqv (π₁ t) = cong π₁ (rr-r-eq eqv t)
rr-r-eq eqv (π₂ t) = cong π₂ (rr-r-eq eqv t)
rr-r-eq eqv (t · s) = app-term-≡ (rr-r-eq eqv t) (rr-r-eq eqv s)
rr-r-eq eqv (ƛ t) = cong ƛ_ (rr-r-eq (eq-lift eqv) t)
        where
                eq-lift : ∀{Δ} → {rs : Ren Γ Δ}{rs' : Ren Δ Θ}{ss : Ren Γ Θ}
                        → (∀{σ} → (x : Γ ∋ σ) → rename rs' (rename rs (` x)) ≡ rename ss (` x))
                        → {σ τ : Type}(x : τ ∷ Γ ∋ σ) → rename (lift rs') (rename (lift rs) (` x)) ≡ rename (lift ss) (` x)
                eq-lift eqv ze = refl
                eq-lift {rs = rs} {rs'} {ss} eqv (su x) = cong `_ (lookupRen (lookupRen x (mapRen su rs)) (lift rs')
                                                                  ≡⟨ cong (λ y → lookupRen y (lift rs')) (lookupRen-map su x refl) ⟩ 
                                                                   lookupRen (lookupRen x rs) (mapRen su rs')
                                                                  ≡⟨ lookupRen-map su (lookupRen x rs) refl ⟩ 
                                                                   su (lookupRen (lookupRen x rs) rs')
                                                                  ≡⟨ cong su (`-elim-≡ (eqv x)) ⟩
                                                                   su (lookupRen x ss)
                                                                  ≡⟨ ≡-sym (lookupRen-map su x refl) ⟩ 
                                                                   lookupRen x (mapRen su ss)
                                                                  ∎)

rename-lift-weaken≡weaken-rename' : ∀{τ} → (ρ : Ren Γ Δ)(x : Γ ∋ σ) → rename (lift {σ = τ} ρ) (weaken (` x)) ≡ weaken (rename ρ (` x))
rename-lift-weaken≡weaken-rename' ρ ze = cong `_ (lookupRen ze (mapRen su ρ)
                                                  ≡⟨ lookupRen-map su {ρ} ze refl ⟩ su (lookupRen ze ρ)
                                                  ≡⟨ ≡-sym (lookupRen-wk (lookupRen ze ρ)) ⟩ lookupRen (lookupRen ze ρ) wk ∎)
rename-lift-weaken≡weaken-rename' ρ (su x) = (` lookupRen (lookupRen x (mapRen su (mapRen su idRen))) (lift ρ))
                                           ≡⟨ cong `_ (cong (λ y → lookupRen y (lift ρ)) (lookupRen-map su x refl)) ⟩ (` lookupRen (lookupRen x (mapRen su idRen)) (mapRen su ρ))
                                           ≡⟨ cong `_ (cong (λ y → lookupRen y (mapRen su ρ)) (lookupRen-wk x)) ⟩ (` lookupRen (su x) (mapRen su ρ))
                                           ≡⟨ cong `_ (lookupRen-map su {ρ} (su x) refl) ⟩ (` su (lookupRen (su x) ρ))
                                           ≡⟨ refl ⟩ weaken' (` lookupRen (su x) ρ)
                                           ≡⟨ ≡-sym (weaken≡weaken' (` lookupRen (su x) ρ)) ⟩ weaken (` lookupRen (su x) ρ) ∎

rename-lift-weaken≡weaken-rename : ∀{τ} → (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → rename (lift {σ = τ} ρ) (weaken t) ≡ weaken (rename ρ t)
rename-lift-weaken≡weaken-rename ρ t = rr-eq (rename-lift-weaken≡weaken-rename' ρ) t

sr-rs-eq : ∀{Δ Δ'} → {ρ : Ren Γ Δ}{ts : Sub Δ Θ}{ss : Sub Γ Δ'}{ρ' : Ren Δ' Θ}
         → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ rename ρ' (subst (` x) ss))
         → {σ : Type}(t : Γ ⊢ σ) → subst (rename ρ t) ts ≡ rename ρ' (subst t ss)
sr-rs-eq eqv (` x) = eqv x
sr-rs-eq eqv yes = refl
sr-rs-eq eqv no = refl
sr-rs-eq eqv ⟨⟩ = refl
sr-rs-eq eqv (t , s) = pair-term-≡ (sr-rs-eq eqv t) (sr-rs-eq eqv s)
sr-rs-eq eqv (π₁ t) = cong π₁ (sr-rs-eq eqv t)
sr-rs-eq eqv (π₂ t) = cong π₂ (sr-rs-eq eqv t)
sr-rs-eq eqv (t · s) = app-term-≡ (sr-rs-eq eqv t) (sr-rs-eq eqv s)
sr-rs-eq eqv (ƛ t) = cong ƛ_ (sr-rs-eq (eq-lift eqv) t)
    where
        eq-lift : ∀{Δ Δ'} → {ρ : Ren Γ Δ}{ts : Sub Δ Θ}{ss : Sub Γ Δ'}{ρ' : Ren Δ' Θ}
                → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (` x)) ts ≡ rename ρ' (subst (` x) ss))
                → {σ τ : Type}(x : τ ∷ Γ ∋ σ) → subst (rename (lift ρ) (` x)) (ts ↑) ≡ rename (lift ρ') (subst (` x) (ss ↑))
        eq-lift {ρ = ρ} {ts} {ss} {ρ'} eqv ze = refl
        eq-lift {ρ = ρ} {ts} {ss} {ρ'} eqv (su x) = lookup (lookupRen x (mapRen su ρ)) (ts ↑)
                                                  ≡⟨ cong (λ y → lookup y (ts ↑)) (lookupRen-map su x refl) ⟩ lookup (lookupRen x ρ) (mapSub weaken ts)
                                                  ≡⟨ lookup-map weaken (lookupRen x ρ) refl ⟩ weaken (lookup (lookupRen x ρ) ts)
                                                  ≡⟨ cong weaken (eqv x) ⟩ weaken (rename ρ' (lookup x ss))
                                                  ≡⟨ ≡-sym (rename-lift-weaken≡weaken-rename ρ' (lookup x ss)) ⟩ rename (lift ρ') (weaken (lookup x ss))
                                                  ≡⟨ cong (rename (lift ρ')) (≡-sym (lookup-map weaken x refl)) ⟩ rename (lift ρ') (lookup x (mapSub weaken ss)) ∎

π₁-subst-eq : (t : Γ ⊢ σ ẋ τ){ts : Sub Γ Δ} → π₁ (subst t ts) ≡ subst (π₁ t) ts
π₁-subst-eq t = refl

pair-subst-eq : (t : Γ ⊢ σ)(s : Γ ⊢ τ){ts : Sub Γ Δ} → (subst t ts , subst s ts) ≡ subst (t , s) ts
pair-subst-eq t s = refl

subst-weaken-↑' : ∀{τ} → (x : Γ ∋ σ)(ts : Sub Γ Δ) → subst (weaken {τ = τ} (` x)) (ts ↑) ≡ weaken (subst (` x) ts)
subst-weaken-↑' ze (t ∷ ts) = refl
subst-weaken-↑' {τ = τ} (su x) (t ∷ ts) = lookup (lookupRen x (mapRen su (mapRen su idRen))) ((t ∷ ts) ↑)
                                ≡⟨ lookup-lookupRen-su-↑ x wk (t ∷ ts) ⟩ weaken (lookup (lookupRen x wk) (t ∷ ts))
                                ≡⟨ ≡-sym (lookup-map weaken (lookupRen x wk) refl) ⟩ lookup (lookupRen x wk) (weaken t ∷ mapSub weaken ts)
                                ≡⟨ lookup-wk x (weaken t) (` ze) (mapSub weaken ts) ⟩ lookup (lookupRen x wk) ((` ze) ∷ mapSub weaken ts)
                                ≡⟨ subst-weaken-↑' x ts ⟩ weaken (lookup x ts) ∎

subst-weaken-↑ : ∀{τ} → (t : Γ ⊢ σ)(ts : Sub Γ Δ) → subst (weaken {τ = τ} t) (ts ↑) ≡ weaken (subst t ts)
subst-weaken-↑ t ts = sr-rs-eq {ρ = wk} {ts ↑} {ts} {wk} (λ x → subst-weaken-↑' x ts) t

lookup-⊙↑-≡ : ∀{σ τ} → (ts : Sub Γ Δ)(ss : Sub Δ Θ)(x : σ ∷ Γ ∋ τ) → lookup x ((ts ↑) ⊙ (ss ↑)) ≡ lookup x ((ts ⊙ ss) ↑)
lookup-⊙↑-≡ ts ss ze = refl
lookup-⊙↑-≡ (t ∷ ts) ss (su ze) = subst-weaken-↑ t ss
lookup-⊙↑-≡ (t ∷ ts) ss (su (su x)) = lookup-⊙↑-≡ ts ss (su x)

⊙↑-≡ : ∀{σ} → (ts : Sub Γ Δ)(ss : Sub Δ Θ) → ((_↑ {σ = σ} ts) ⊙ (ss ↑)) ≡ ((ts ⊙ ss) ↑)
⊙↑-≡ {Γ = Γ} {σ = σ} ts ss = eqSub ((ts ↑) ⊙ (ss ↑)) ((ts ⊙ ss) ↑) (λ n → lookup-⊙↑-≡ ts ss n)

subsub : (t : Γ ⊢ σ){ts : Sub Γ Δ}{ss : Sub Δ Θ} → subst (subst t ts) ss ≡ subst t (ts ⊙ ss)
subsub (` ze) {t ∷ ts} = refl
subsub (` su n) {t ∷ ts} = subsub (` n)
subsub yes = refl
subsub no = refl
subsub ⟨⟩ = refl
subsub (t , s) = pair-term-≡ (subsub t) (subsub s)
subsub (π₁ t) = cong π₁ (subsub t)
subsub (π₂ t) = cong π₂ (subsub t)
subsub (t · s) = app-term-≡ (subsub t) (subsub s)
subsub (ƛ t) {ts} {ss} = cong ƛ_ (subst (subst t (ts ↑)) (ss ↑)
                                      ≡⟨ subsub t {ts ↑} {ss ↑} ⟩ subst t ((ts ↑) ⊙ (ss ↑))
                                      ≡⟨ cong (subst t) (⊙↑-≡ ts ss) ⟩ subst t ((ts ⊙ ss) ↑) ∎)

subst-weaken-idRen' : ∀{τ σ} → (x : Γ ∋ σ){s : Γ ⊢ τ} → subst (weaken {τ = τ} (` x)) (s ∷ idSub) ≡ rename idRen (` x)
subst-weaken-idRen' ze = refl
subst-weaken-idRen' (su x) {s} = lookup (lookupRen x (mapRen su (mapRen su idRen))) (s ∷ (idSub ↑))
                          ≡⟨ cong (λ y → lookup y (s ∷ (idSub ↑))) (lookupRen-map su x refl) ⟩ lookup (lookupRen x (mapRen su idRen)) (idSub ↑)
                          ≡⟨ lookup-idSub {x = lookupRen x (mapRen su idRen)} ⟩ (` lookupRen x (mapRen su idRen)) ∎

subst-weaken-idRen : ∀{τ} → (t : Γ ⊢ σ){s : Γ ⊢ τ} → subst (weaken {τ = τ} t) (s ∷ idSub) ≡ rename idRen t
subst-weaken-idRen t {s} = sr-r-eq {ρ = wk} {s ∷ idSub} {idRen} (λ x → subst-weaken-idRen' x {s}) t


subst-weaken-idSub : ∀{τ} → (t : Γ ⊢ σ){s : Γ ⊢ τ} → subst (weaken {τ = τ} t) (s ∷ idSub) ≡ t
subst-weaken-idSub t {s} = subst (weaken t) (s ∷ idSub)
                         ≡⟨ subst-weaken-idRen t ⟩ rename idRen t
                         ≡⟨ rename-idRen t ⟩ t ∎

_↑⊙_∷id : (ts : Sub Γ Δ)(s : Δ ⊢ σ) → ((ts ↑) ⊙ (s ∷ idSub)) ≡ s ∷ ts
_↑⊙_∷id {.[]} [] s = cong (s ∷_) refl
_↑⊙_∷id {.(_ ∷ _)} (t ∷ ts) s = cong (s ∷_) (∷-sub-eq (subst-weaken-idSub t) (sub-head-eq-elim (ts ↑⊙ s ∷id)))

lem[sub1] : (t : σ ∷ Γ ⊢ τ)(ts : Sub Γ Δ)(s : Δ ⊢ σ) → (subst t (ts ↑) [ s /x]) ≡ (subst t (s ∷ ts))
lem[sub1] t ts s = subst t (ts ↑) [ s /x]
                            ≡⟨ refl ⟩ subst (subst t (ts ↑)) (s ∷ idSub)
                            ≡⟨ subsub t ⟩ subst t ((ts ↑) ⊙ (s ∷ idSub))
                            ≡⟨ cong (subst t) (ts ↑⊙ s ∷id) ⟩ subst t (s ∷ ts) ∎

subst-rename≡rename-subst' : ∀{σ} → (ρ : Ren Γ Δ){s : Γ ⊢ τ}(x : τ ∷ Γ ∋ σ) → subst (rename (lift ρ) (` x)) (rename ρ s ∷ idSub) ≡ rename ρ (subst (` x) (s ∷ idSub))
subst-rename≡rename-subst' ρ ze = refl
subst-rename≡rename-subst' ρ {s} (su x) = lookup (lookupRen x (mapRen su ρ)) (rename ρ s ∷ idSub)
                                        ≡⟨ cong (λ y → lookup y (rename ρ s ∷ idSub)) (lookupRen-map su x refl) ⟩ 
                                          lookup (lookupRen x ρ) idSub
                                        ≡⟨ lookup-idSub {x = lookupRen x ρ} ⟩ 
                                         (` lookupRen x ρ)
                                        ≡⟨ refl ⟩
                                          rename ρ (` x)
                                        ≡⟨ cong (rename ρ) (≡-sym (lookup-idSub {x = x})) ⟩ 
                                          rename ρ (lookup x idSub)
                                        ∎

subst-rename≡rename-subst : (ρ : Ren Γ Δ)(t : τ ∷ Γ ⊢ σ){s : Γ ⊢ τ} → subst (rename (lift ρ) t) (rename ρ s ∷ idSub) ≡ rename ρ (subst t (s ∷ idSub))
subst-rename≡rename-subst ρ t {s} = sr-rs-eq {ρ = lift ρ} {rename ρ s ∷ idSub} {s ∷ idSub} {ρ} (subst-rename≡rename-subst' ρ) t

rename-concatRen≡rename-rename' : (ρ : Ren Γ Δ)(ρ' : Ren Δ Θ){σ : Type}(x : Γ ∋ σ) → rename (concatRen ρ ρ') (` x) ≡ rename ρ' (rename ρ (` x))
rename-concatRen≡rename-rename' {Γ} ρ ρ' x = cong `_ (lookupRen x (concatRen ρ ρ')
                                                      ≡⟨ lookupRen-map {Γ = Γ} (λ y → lookupRen y ρ') {ρ} x refl ⟩
                                                       lookupRen (lookupRen x ρ) ρ'
                                                      ∎)

rename-concatRen≡rename-rename : (ρ : Ren Γ Δ)(ρ' : Ren Δ Θ)(t : Γ ⊢ σ) → rename (concatRen ρ ρ') t ≡ rename ρ' (rename ρ t)
rename-concatRen≡rename-rename ρ ρ' t = ≡-sym (rr-r-eq {rs = ρ} {ρ'} {concatRen ρ ρ'} (λ x → ≡-sym (rename-concatRen≡rename-rename' ρ ρ' x)) t)

srs-s-eq : ∀{Δ Δ'} → {ts : Sub Γ Δ}{ρ : Ren Δ Δ'}{ss : Sub Δ' Θ}{us : Sub Γ Θ}
         → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (subst (` x) ts)) ss ≡ (subst (` x) us))
         → {σ : Type}(t : Γ ⊢ σ) → subst (rename ρ (subst t ts)) ss ≡ (subst t us)
srs-s-eq eqv (` x) = eqv x
srs-s-eq eqv yes = refl
srs-s-eq eqv no = refl
srs-s-eq eqv ⟨⟩ = refl
srs-s-eq eqv (t , s) = pair-term-≡ (srs-s-eq eqv t) (srs-s-eq eqv s)
srs-s-eq eqv (π₁ t) = cong π₁ (srs-s-eq eqv t)
srs-s-eq eqv (π₂ t) = cong π₂ (srs-s-eq eqv t)
srs-s-eq eqv (t · s) = app-term-≡ (srs-s-eq eqv t) (srs-s-eq eqv s)
srs-s-eq eqv (ƛ t) = cong ƛ_ (srs-s-eq (eq-lift eqv) t)
        where
                eq-lift : ∀{Δ Δ'} → {ts : Sub Γ Δ}{ρ : Ren Δ Δ'}{ss : Sub Δ' Θ}{us : Sub Γ Θ}
                        → (∀{σ} → (x : Γ ∋ σ) → subst (rename ρ (subst (` x) ts)) ss ≡ (subst (` x) us))
                        → {σ τ : Type}(x : τ ∷ Γ ∋ σ) → subst (rename (lift ρ) (subst (` x) (ts ↑))) (ss ↑) ≡ subst (` x) (us ↑)
                eq-lift {ts = ts} {ρ} {ss} {us} eqv ze = refl
                eq-lift {ts = ts} {ρ} {ss} {us} eqv (su x) = subst (rename (lift ρ) (lookup x (mapSub weaken ts))) (ss ↑)
                                                           ≡⟨ cong (λ t → subst (rename (lift ρ) t) (ss ↑)) (lookup-map weaken x refl) ⟩ 
                                                             subst (rename (lift ρ) (weaken (lookup x ts))) (ss ↑)
                                                           ≡⟨ cong (λ t → subst t (ss ↑)) (rename-lift-weaken≡weaken-rename ρ (lookup x ts)) ⟩ 
                                                             subst (weaken (rename ρ (lookup x ts))) (ss ↑)
                                                           ≡⟨ subst-weaken-↑ (rename ρ (lookup x ts)) ss ⟩ 
                                                             weaken (subst (rename ρ (lookup x ts)) ss)
                                                           ≡⟨ cong weaken (eqv x) ⟩ 
                                                             weaken (lookup x us)
                                                           ≡⟨ ≡-sym (lookup-map weaken x refl) ⟩ 
                                                             lookup x (mapSub weaken us) 
                                                           ∎

subst-rename-lift-subst' : ∀{Γ Δ Θ σ τ} → (ρ : Ren Δ Θ)(ts : Sub Γ Δ)(s : Θ ⊢ σ)(x : σ ∷ Γ ∋ τ) → subst (rename (lift ρ) (subst (` x) (ts ↑))) (s ∷ idSub) ≡ subst (` x) (s ∷ mapSub (rename ρ) ts)
subst-rename-lift-subst' ρ ts s ze = refl
subst-rename-lift-subst' ρ ts s (su x) = subst (rename (lift ρ) (lookup x (mapSub weaken ts))) (s ∷ idSub)
                  ≡⟨ cong (λ t → subst (rename (lift ρ) t) (s ∷ idSub)) (lookup-map weaken x refl) ⟩ 
                    subst (rename (lift ρ) (weaken (lookup x ts))) (s ∷ idSub)
                  ≡⟨ cong (λ t → subst t (s ∷ idSub)) (rename-lift-weaken≡weaken-rename ρ (lookup x ts)) ⟩ 
                    subst (weaken (rename ρ (lookup x ts))) (s ∷ idSub)
                  ≡⟨ subst-weaken-idSub (rename ρ (lookup x ts)) {s} ⟩ 
                    rename ρ (lookup x ts)
                  ≡⟨ ≡-sym (lookup-map (rename ρ) x refl) ⟩ 
                    lookup x (mapSub (rename ρ) ts) 
                  ∎
subst-rename-lift-subst : ∀{Γ Δ Θ σ τ} → (ρ : Ren Δ Θ)(ts : Sub Γ Δ)(t : σ ∷ Γ ⊢ τ)(s : Θ ⊢ σ) → (rename (lift ρ) (subst t (ts ↑)) [ s /x]) ≡ subst t (s ∷ mapSub (rename ρ) ts)
subst-rename-lift-subst ρ ts t s = srs-s-eq {ts = ts ↑} {lift ρ} {s ∷ idSub} {s ∷ mapSub (rename ρ) ts} (subst-rename-lift-subst' ρ ts s) t