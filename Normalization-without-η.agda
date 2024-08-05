module Normalization-without-η where

open import STLC
open import STLC.Reduction
open import STLC.Normal-without-η

-- Defining Computability Structures in accordance with logical relation
Normalizable : Γ ⊢ σ → Set
Normalizable {Γ} {σ} t = Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')

renameN : {t : Γ ⊢ σ}(ρ : Ren Γ Δ) → Normalizable t → Normalizable (rename ρ t)
renameN ρ (t' , t→t' , nt') = rename ρ t' , ξ-rename* ρ t→t' , rename-nf ρ nt'

ξ-ƛN : {t : σ ∷ Γ ⊢ τ} → Normalizable t → Normalizable (ƛ t)
ξ-ƛN (t' , t→t' , nt') = (ƛ t') , ξ-ƛ* t→t' , (ƛ nt')

Comp : (σ : Type)(t : Γ ⊢ σ) → Set
Comp {Γ} Ans t = Normalizable t
Comp {Γ} 𝟙 t = Normalizable t
Comp {Γ} (σ ẋ τ) t = Normalizable t × Comp σ (π₁ t) × Comp τ (π₂ t)
Comp {Γ} (σ ⇒ τ) t = Normalizable t × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Comp τ (rename ρ t · a))

-- Shift computability structure by βη-conversion
comp-backward : (σ : Type){t t' : Γ ⊢ σ} → t →β t' → Comp σ t' → Comp σ t
comp-backward Ans t→t' (t'' , t'→t'' , nt'') = t'' , t→t' ‣ t'→t'' , nt''
comp-backward 𝟙 t→t' (t'' , t'→t'' , nt'') = t'' , t→t' ‣ t'→t'' , nt''
comp-backward (σ ẋ τ) t→t' ((t'' , t'→t'' , nt'') , c₁ , c₂) = (t'' , t→t' ‣ t'→t'' , nt'') , comp-backward σ (ξ-π₁ t→t') c₁ , comp-backward τ (ξ-π₂ t→t') c₂
comp-backward (σ ⇒ τ) t→t' ((t' , t'→t'' , nt'') , c) = (t' , t→t' ‣ t'→t'' , nt'') , λ Θ ρ a c' → comp-backward τ (ξ-·₁ (ξ-rename ρ t→t')) (c Θ ρ a c')

comp-backward* : (σ : Type){t t' : Γ ⊢ σ} → t →β* t' → Comp σ t' → Comp σ t
comp-backward* σ ✦ c = c
comp-backward* σ (t→u ‣ u→t') c = comp-backward σ t→u (comp-backward* σ u→t' c)

-- Define reification and reflection
reify : {t : Γ ⊢ σ} → Comp σ t → Normalizable t
reify {σ = Ans} = id
reify {σ = 𝟙} = id
reify {σ = σ ẋ τ} = pr₁
reify {σ = σ ⇒ τ} = pr₁

reflect : {t : Γ ⊢ σ} → Neutral Γ σ t → Comp σ t
reflect {σ = Ans} ne = _ , ✦ , (‘ ne)
reflect {σ = 𝟙} ne = _ , ✦ , (‘ ne)
reflect {σ = σ ẋ τ} ne = (_ , ✦ , (‘ ne)) , reflect (π₁ ne) , reflect (π₂ ne)
reflect {σ = σ ⇒ τ} ne = (_ , ✦ , (‘ ne)) , λ Θ ρ a c → let (a' , a→a' , na') = reify c in comp-backward* _ (ξ-·* ✦ a→a') (reflect (rename-ne ρ ne · na'))

-- Show that renaming preserves computability structures
rename-comp : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t) 
rename-comp {σ = Ans} ρ _ = renameN ρ
rename-comp {σ = 𝟙} ρ _ = renameN ρ
rename-comp {σ = σ ẋ τ} ρ t (Nt , c₁ , c₂) = renameN ρ Nt , rename-comp ρ (π₁ t) c₁ , rename-comp ρ (π₂ t) c₂
rename-comp {σ = σ ⇒ τ} ρ t (Nt , c) = renameN ρ Nt ,
                                       λ Θ ρ' a c' → transport (λ y → Comp τ (y · a)) (rename-concatRen≡rename-rename ρ ρ' t)
                                                               (c Θ (concatRen ρ ρ') a c')

-- shorthand for substitution
infix 25 _[_]
_[_] : Γ ⊢ σ → Sub Γ Δ → Δ ⊢ σ
t [ ts ] = subst t ts

-- list of computability structures for each term in a substitution
data ⟦_⟧ᶜ : (Γ : Cxt) → Sub Γ Δ → Set where
    [] : ∀{Δ} → ⟦ [] ⟧ᶜ ([] {Δ})
    _∷_ : ∀{σ} → {t : Δ ⊢ σ}{ts : Sub Γ Δ} → Comp σ t → ⟦ Γ ⟧ᶜ ts → ⟦ (σ ∷ Γ) ⟧ᶜ (t ∷ ts)

lookupᶜ : {ts : Sub Γ Δ}(x : Γ ∋ σ) → ⟦ Γ ⟧ᶜ ts → Comp σ (lookup x ts)
lookupᶜ ze (c ∷ _) = c
lookupᶜ (su x) (_ ∷ cs) = lookupᶜ x cs

mapᶜ : (fₜ : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ)(fₛ : ∀{σ} → {t : Δ ⊢ σ} → Comp σ t → Comp σ (fₜ t)) → {ts : Sub Γ Δ} → ⟦ Γ ⟧ᶜ ts → ⟦ Γ ⟧ᶜ (mapSub fₜ ts)
mapᶜ fₜ fₛ [] = []
mapᶜ fₜ fₛ (c ∷ cs) = fₛ c ∷ mapᶜ fₜ fₛ cs

renameᶜ : (ρ : Ren Δ Θ){ts : Sub Γ Δ} → ⟦ Γ ⟧ᶜ ts → ⟦ Γ ⟧ᶜ (mapSub (rename ρ) ts)
renameᶜ ρ cs = mapᶜ (rename ρ) (λ {σ} {t} → rename-comp ρ t) cs

-- Define computability morphisms assigned for each term
⟦_⟧ : (t : Γ ⊢ σ)(Δ : Cxt)(ts : Sub Γ Δ)(cs : ⟦ Γ ⟧ᶜ ts) → Comp σ (t [ ts ])
⟦ ` x ⟧ Δ ts cs = lookupᶜ x cs
⟦ yes ⟧ Δ ts cs = yes , ✦ , yes
⟦ no ⟧ Δ ts cs = no , ✦ , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩
⟦ t , s ⟧ Δ ts cs with reify (⟦ t ⟧ Δ ts cs) | reify (⟦ s ⟧ Δ ts cs)
... | t' , t[ts]→t' , nt' | s' , s[ts]→s' , ns' = ((t' , s') , ξ-,* t[ts]→t' s[ts]→s' , (nt' , ns')) ,
                                                  comp-backward _ β-π₁ (⟦ t ⟧ Δ ts cs) ,
                                                  comp-backward _ β-π₂ (⟦ s ⟧ Δ ts cs)
⟦ π₁ t ⟧ Δ ts cs = pr₁ (pr₂ (⟦ t ⟧ Δ ts cs))
⟦ π₂ t ⟧ Δ ts cs = pr₂ (pr₂ (⟦ t ⟧ Δ ts cs))
⟦ t · s ⟧ Δ ts cs = transport (λ y → Comp _ (y · (s [ ts ]))) (rename-idRen (t [ ts ])) (pr₂ (⟦ t ⟧ Δ ts cs) Δ idRen (s [ ts ]) (⟦ s ⟧ Δ ts cs))
⟦ ƛ_ {σ = σ} t ⟧ Δ ts cs = ξ-ƛN (reify (⟦ t ⟧ (σ ∷ Δ) ((` ze) ∷ mapSub weaken ts) (reflect (` ze) ∷ renameᶜ wk cs))) ,
                          λ Θ ρ a c → comp-backward _ β-ƛ (transport (Comp _) (≡-sym (subst-rename-lift-subst ρ ts t a)) 
                                                                     (⟦ t ⟧ Θ (a ∷ mapSub (rename ρ) ts) (c ∷ renameᶜ ρ cs)))

-- reflection for each term in a neutral substitution
reflectᶜ : (Γ Δ : Cxt)(ts : Sub Γ Δ) → NeutralSub ts → ⟦ Γ ⟧ᶜ ts
reflectᶜ [] Δ .[] [] = []
reflectᶜ (σ ∷ Γ) Δ (t ∷ ts) (nt ∷ ns) = reflect nt ∷ reflectᶜ Γ Δ ts ns

--  evaluate a term to its computability structure
eval : (t : Γ ⊢ σ) → Comp σ t
eval {Γ} {σ} t = transport (Comp σ) (subst-idSub {t = t}) (⟦ t ⟧ Γ idSub (reflectᶜ Γ Γ idSub idSub-is-neutral))
     
-- normalization by evaluation
normalize : (t : Γ ⊢ σ) → Normalizable t
normalize {Γ} {σ} t = reify (eval t)

-- test term
test-term : [] ⊢ Ans
test-term = (ƛ (` ze)) · (π₁ (π₂ (yes , ((ƛ (` ze)) · no)) , ⟨⟩))