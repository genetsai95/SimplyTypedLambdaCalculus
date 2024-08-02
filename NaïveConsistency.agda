module NaïveConsistency where

open import Prelude
open import STLC
open import STLC.Reduction

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

∷-cxt-eq : {c c' : ⟦ σ ⟧ᵗ}{cs cs' : ⟦ Γ ⟧ᶜ} → c ≡ c' → cs ≡ cs' → _≡_ {X = ⟦ σ ∷ Γ ⟧ᶜ} (c ∷ cs) (c' ∷ cs')
∷-cxt-eq refl refl = refl

lookupCxt : Γ ∋ σ → ⟦ Γ ⟧ᶜ → ⟦ σ ⟧ᵗ
lookupCxt ze (t ∷ _) = t
lookupCxt (su n) (_ ∷ ts) = lookupCxt n ts

eqᶜ : (ts ss : ⟦ Γ ⟧ᶜ) → (∀{σ} → (x : Γ ∋ σ) → lookupCxt x ts ≡ lookupCxt x ss) → ts ≡ ss
eqᶜ [] [] _ = refl
eqᶜ (t ∷ ts) (s ∷ ss) eqx with eqx ze
... | refl = cong (t ∷_) (eqᶜ ts ss (λ x → eqx (su x)))

renameᶜ : Ren Γ Δ → ⟦ Δ ⟧ᶜ → ⟦ Γ ⟧ᶜ
renameᶜ [] cs = []
renameᶜ (r ∷ rs) cs = lookupCxt r cs ∷ renameᶜ rs cs

lookupCxt-lookupRen : (ρ : Ren Γ Δ){σ : Type}(x : Γ ∋ σ)(cs : ⟦ Δ ⟧ᶜ) → lookupCxt (lookupRen x ρ) cs ≡ lookupCxt x (renameᶜ ρ cs)
lookupCxt-lookupRen (_ ∷ _) ze cs = refl
lookupCxt-lookupRen (_ ∷ ρ) (su x) cs = lookupCxt-lookupRen ρ x cs

renameᶜ-mapRen-su : (ρ : Ren Γ Δ)(cs : ⟦ Δ ⟧ᶜ){c : ⟦ σ ⟧ᵗ} → renameᶜ (mapRen su ρ) (c ∷ cs) ≡ renameᶜ ρ cs
renameᶜ-mapRen-su [] cs = refl
renameᶜ-mapRen-su (r ∷ ρ) cs = cong (lookupCxt r cs ∷_) (renameᶜ-mapRen-su ρ cs)

renameᶜ-idRen : (cs : ⟦ Γ ⟧ᶜ) → renameᶜ idRen cs ≡ cs
renameᶜ-idRen [] = refl
renameᶜ-idRen (c ∷ cs) = cong (c ∷_) (renameᶜ (mapRen su idRen) (c ∷ cs)
                                      ≡⟨ renameᶜ-mapRen-su idRen cs ⟩ renameᶜ idRen cs
                                      ≡⟨ renameᶜ-idRen cs ⟩ cs ∎)

renameᶜ-wk : ∀{σ} → (cs : ⟦ Γ ⟧ᶜ){c : ⟦ σ ⟧ᵗ} → renameᶜ (wk {σ = σ}) (c ∷ cs) ≡ cs
renameᶜ-wk cs {c} = renameᶜ wk (c ∷ cs)
                  ≡⟨ renameᶜ-mapRen-su idRen cs ⟩ renameᶜ idRen cs
                  ≡⟨ renameᶜ-idRen cs ⟩ cs ∎

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

⟦rename⟧ : (ρ : Ren Γ Δ)(t : Γ ⊢ σ)(cs : ⟦ Δ ⟧ᶜ) → ⟦ rename ρ t ⟧ cs ≡ ⟦ t ⟧ (renameᶜ ρ cs)
⟦rename⟧ ρ (` x) cs = lookupCxt-lookupRen ρ x cs
⟦rename⟧ ρ yes cs = refl
⟦rename⟧ ρ no cs = refl
⟦rename⟧ ρ ⟨⟩ cs = refl
⟦rename⟧ ρ (t , s) cs = pair-≡ (⟦rename⟧ ρ t cs) (⟦rename⟧ ρ s cs)
⟦rename⟧ ρ (π₁ t) cs = cong pr₁ (⟦rename⟧ ρ t cs)
⟦rename⟧ ρ (π₂ t) cs = cong pr₂ (⟦rename⟧ ρ t cs)
⟦rename⟧ ρ (t · s) cs = app-≡ (⟦rename⟧ ρ t cs) (⟦rename⟧ ρ s cs)
⟦rename⟧ ρ (ƛ t) cs = fx (λ u → ⟦ rename (lift ρ) t ⟧ (u ∷ cs)
                            ≡⟨ ⟦rename⟧ (lift ρ) t (u ∷ cs) ⟩ 
                                ⟦ t ⟧ (u ∷ renameᶜ (mapRen su ρ) (u ∷ cs))
                            ≡⟨ cong (λ cs' → ⟦ t ⟧ (u ∷ cs')) (renameᶜ-mapRen-su ρ cs) ⟩ 
                                ⟦ t ⟧ (u ∷ renameᶜ ρ cs)
                            ∎)

⟦rename-lift-wk⟧ : ∀{σ τ σ'} → (t : τ ∷ Γ ⊢ σ)(c : ⟦ τ ⟧ᵗ)(cs : ⟦ Γ ⟧ᶜ){c' : ⟦ σ' ⟧ᵗ} → ⟦ rename (lift {σ = τ} (wk {σ = σ'})) t ⟧ (c ∷ (c' ∷ cs)) ≡ ⟦ t ⟧ (c ∷ cs)
⟦rename-lift-wk⟧ t c cs {c'} = ⟦ rename (lift wk) t ⟧ (c ∷ c' ∷ cs)
                            ≡⟨ ⟦rename⟧ (lift wk) t (c ∷ c' ∷ cs) ⟩ 
                              ⟦ t ⟧ (c ∷ renameᶜ (mapRen su wk) (c ∷ c' ∷ cs))
                            ≡⟨ cong (λ cs' → ⟦ t ⟧ (c ∷ cs')) (renameᶜ-mapRen-su wk (c' ∷ cs) {c}) ⟩ 
                              ⟦ t ⟧ (c ∷ renameᶜ wk (c' ∷ cs))
                            ≡⟨ cong (λ cs' → ⟦ t ⟧ (c ∷ cs')) (renameᶜ-wk cs) ⟩ 
                              ⟦ t ⟧ (c ∷ cs)
                            ∎

⟦weaken⟧ : ∀{σ'} → (t : Γ ⊢ σ)(cs : ⟦ Γ ⟧ᶜ)(c : ⟦ σ' ⟧ᵗ) → ⟦ weaken t ⟧ (c ∷ cs) ≡ ⟦ t ⟧ cs
⟦weaken⟧ (` x) cs c = lookupCxt (lookupRen x wk) (c ∷ cs)
                   ≡⟨ cong (λ y → lookupCxt y (c ∷ cs)) (lookupRen-wk x) ⟩ lookupCxt (su x) (c ∷ cs)
                   ≡⟨ refl ⟩ lookupCxt x cs ∎
⟦weaken⟧ yes cs c = refl
⟦weaken⟧ no cs c = refl
⟦weaken⟧ ⟨⟩ cs c = refl
⟦weaken⟧ (t , s) cs c = pair-≡ (⟦weaken⟧ t cs c) (⟦weaken⟧ s cs c)
⟦weaken⟧ (π₁ t) cs c = cong pr₁ (⟦weaken⟧ t cs c)
⟦weaken⟧ (π₂ t) cs c = cong pr₂ (⟦weaken⟧ t cs c)
⟦weaken⟧ (t · s) cs c = app-≡ (⟦weaken⟧ t cs c) (⟦weaken⟧ s cs c)
⟦weaken⟧ (ƛ t) cs c = fx λ y → ⟦ rename (lift wk) t ⟧ (y ∷ (c ∷ cs)) ≡⟨ ⟦rename-lift-wk⟧ t y cs ⟩ ⟦ t ⟧ (y ∷ cs) ∎

⟦_⟧ₛ : (ts : Sub Δ Γ) → ⟦ Γ ⟧ᶜ → ⟦ Δ ⟧ᶜ
⟦ [] ⟧ₛ _ = []
⟦ t ∷ ts ⟧ₛ cs = ⟦ t ⟧ cs ∷ ⟦ ts ⟧ₛ cs

⟦map-weaken⟧ₛ : ∀{σ} → (ts : Sub Δ Γ)(cs : ⟦ Γ ⟧ᶜ)(u : ⟦ σ ⟧ᵗ) → ⟦ mapSub weaken ts ⟧ₛ (u ∷ cs) ≡ ⟦ ts ⟧ₛ cs
⟦map-weaken⟧ₛ [] cs u = refl
⟦map-weaken⟧ₛ (t ∷ ts) cs u = ∷-cxt-eq (⟦weaken⟧ t cs u) (⟦map-weaken⟧ₛ ts cs u)

⟦idSub⟧ₛ : (ts : ⟦ Γ ⟧ᶜ) → ⟦ idSub ⟧ₛ ts ≡ ts
⟦idSub⟧ₛ [] = refl
⟦idSub⟧ₛ (t ∷ ts) = cong (t ∷_) (⟦ mapSub weaken idSub ⟧ₛ (t ∷ ts)
                                ≡⟨ ⟦map-weaken⟧ₛ idSub ts t ⟩ ⟦ idSub ⟧ₛ ts
                                ≡⟨ ⟦idSub⟧ₛ ts ⟩ ts ∎)

lem[subst-itp] : (ts : Sub Γ Δ)(t : Γ ⊢ σ)(cs : ⟦ Δ ⟧ᶜ) → ⟦ subst t ts ⟧ cs ≡ ⟦ t ⟧ (⟦ ts ⟧ₛ cs)
lem[subst-itp] (t ∷ ts) (` ze) cs = refl
lem[subst-itp] (t ∷ ts) (` su x) cs = lem[subst-itp] ts (` x) cs
lem[subst-itp] ts yes cs = refl
lem[subst-itp] ts no cs = refl
lem[subst-itp] ts ⟨⟩ cs = refl
lem[subst-itp] ts (t , s) cs = pair-≡ (lem[subst-itp] ts t cs) (lem[subst-itp] ts s cs)
lem[subst-itp] ts (π₁ t) cs = cong pr₁ (lem[subst-itp] ts t cs)
lem[subst-itp] ts (π₂ t) cs = cong pr₂ (lem[subst-itp] ts t cs)
lem[subst-itp] ts (t · s) cs = app-≡ (lem[subst-itp] ts t cs) (lem[subst-itp] ts s cs)
lem[subst-itp] ts (ƛ t) cs = fx λ u → ⟦ subst t (ts ↑) ⟧ (u ∷ cs)
                                    ≡⟨ lem[subst-itp] (ts ↑) t (u ∷ cs) ⟩ 
                                      ⟦ t ⟧ (u ∷ ⟦ mapSub weaken ts ⟧ₛ (u ∷ cs))
                                    ≡⟨ cong (λ cs' → ⟦ t ⟧ (u ∷ cs')) (⟦map-weaken⟧ₛ ts cs u) ⟩ 
                                      ⟦ t ⟧ (u ∷ ⟦ ts ⟧ₛ cs)
                                    ∎

lem[sub1-itp] : (t : τ ∷ Γ ⊢ σ)(s : Γ ⊢ τ){ts : ⟦ Γ ⟧ᶜ} → ⟦ subst t (s ∷ idSub) ⟧ ts ≡ ⟦ t ⟧ (⟦ s ⟧ ts ∷ ts)
lem[sub1-itp] t s {ts} = ⟦ subst t (s ∷ idSub) ⟧ ts
                       ≡⟨ lem[subst-itp] (s ∷ idSub) t ts ⟩ 
                         ⟦ t ⟧ (⟦ s ⟧ ts ∷ ⟦ idSub ⟧ₛ ts)
                       ≡⟨ cong (λ ts' → ⟦ t ⟧ (⟦ s ⟧ ts ∷ ts')) 
                         (⟦idSub⟧ₛ ts) ⟩ ⟦ t ⟧ (⟦ s ⟧ ts ∷ ts)
                       ∎

⟦β→⟧ : {a b : Γ ⊢ σ} → a →β b → ⟦ a ⟧ =f= ⟦ b ⟧
⟦β→⟧ β-π₁ u = refl
⟦β→⟧ β-π₂ u = refl
⟦β→⟧ (ξ-,₁ {s = s} t→t') u = cong (_, ⟦ s ⟧ u) (⟦β→⟧ t→t' u)
⟦β→⟧ (ξ-,₂ {t = t} s→s') u = cong (⟦ t ⟧ u ,_) (⟦β→⟧ s→s' u)
⟦β→⟧ (ξ-π₁ t→t') u = cong pr₁ (⟦β→⟧ t→t' u)
⟦β→⟧ (ξ-π₂ t→t') u = cong pr₂ (⟦β→⟧ t→t' u)
⟦β→⟧ (β-ƛ {t = t} {s = s}) u = ≡-sym (  ⟦ subst t (s ∷ idSub) ⟧ u
                                    ≡⟨ lem[sub1-itp] t s ⟩
                                       ⟦ t ⟧ (⟦ s ⟧ u ∷ u) 
                                    ∎)
⟦β→⟧ (ξ-·₁ {s = s} t→t') u = cong (λ y → y (⟦ s ⟧ u)) (⟦β→⟧ t→t' u)
⟦β→⟧ (ξ-·₂ {t = t} t→t') u = cong (⟦ t ⟧ u) (⟦β→⟧ t→t' u)
⟦β→⟧ (ξ-ƛ t→t') u = fx λ x → ⟦β→⟧ t→t' (x ∷ u)

⟦β→*⟧ : {a b : Γ ⊢ σ} → a →β* b → ⟦ a ⟧ =f= ⟦ b ⟧
⟦β→*⟧ ✦ u = refl
⟦β→*⟧ (r ‣ rs) u = ftrans (⟦β→⟧ r) (⟦β→*⟧ rs) u

thm[consistency] : {a b : Γ ⊢ σ} → Γ ⊢ a ≐ b ∶ σ → ⟦ a ⟧ =f= ⟦ b ⟧
thm[consistency] (β-red rs) = ⟦β→*⟧ rs
thm[consistency] (symⱼ eq) = fsym (thm[consistency] eq)
thm[consistency] (transⱼ eq eq') = ftrans (thm[consistency] eq) (thm[consistency] eq')

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