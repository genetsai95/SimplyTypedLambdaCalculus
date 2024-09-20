module NaïveNormalization where

open import STLC
open import STLC.Conversion
open import STLC.Normal

-- Defining Computability Structures for each type
Normalizable : Γ ⊢ σ → Set
Normalizable {Γ} {σ} t = Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')

Comp : (σ : Type)(t : Γ ⊢ σ) → Set
Comp {Γ} Ans t = Normalizable t
Comp {Γ} 𝟙 t = Normalizable t
Comp {Γ} (σ ẋ τ) t = Comp σ (π₁ t) × Comp τ (π₂ t)
Comp {Γ} (σ ⇒ τ) t = (Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Comp τ (rename ρ t · a)


-- Shift computability structure by βη-conversion
comp-backward : (σ : Type){t t' : Γ ⊢ σ} → t ⟶ t' → Comp σ t' → Comp σ t
comp-backward Ans t→t' (t'' , t'→t'' , nt'') = t'' , t→t' ‣ t'→t'' , nt''
comp-backward 𝟙 t→t' _ = ⟨⟩ , η-⟨⟩ ‣ ✦ , ⟨⟩
comp-backward (σ ẋ τ) t→t' (c₁ , c₂) = comp-backward σ (ξ-π₁ t→t') c₁ , comp-backward τ (ξ-π₂ t→t') c₂
comp-backward (σ ⇒ τ) t→t' c = λ Θ ρ a c' → comp-backward τ (ξ-·₁ (ξ-rename ρ t→t')) (c Θ ρ a c')

comp-backward⋆ : (σ : Type){t t' : Γ ⊢ σ} → t ⟶⋆ t' → Comp σ t' → Comp σ t
comp-backward⋆ σ ✦ c = c
comp-backward⋆ σ (t→u ‣ u→t') c = comp-backward σ t→u (comp-backward⋆ σ u→t' c)


-- Show that renaming preserves computability structures
rename-comp : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
rename-comp {σ = Ans} ρ t (t' , t→t' , nt') = rename ρ t' , ξ-rename⋆ ρ t→t' , rename-nf ρ nt'
rename-comp {σ = 𝟙} ρ t (t' , t→t' , nt') = rename ρ t' , ξ-rename⋆ ρ t→t' , rename-nf ρ nt'
rename-comp {σ = σ ẋ τ} ρ t (c₁ , c₂) = rename-comp ρ (π₁ t) c₁ , rename-comp ρ (π₂ t) c₂
rename-comp {σ = σ ⇒ τ} ρ t c = λ Θ ρ' a c' → transport (λ y → Comp τ (y · a)) (rename-concatRen≡rename-rename ρ ρ' t)
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
⟦ t , s ⟧ Δ ts cs = comp-backward _ β-π₁ (⟦ t ⟧ Δ ts cs) , comp-backward _ β-π₂ (⟦ s ⟧ Δ ts cs)
⟦ π₁ t ⟧ Δ ts cs = pr₁ (⟦ t ⟧ Δ ts cs)
⟦ π₂ t ⟧ Δ ts cs = pr₂ (⟦ t ⟧ Δ ts cs)
⟦ _·_ {_} {σ} {τ} t s ⟧ Δ ts cs = transport (λ y → Comp τ (y · (s [ ts ]))) (rename-idRen (t [ ts ]))
                                           (⟦ t ⟧ Δ ts cs _ idRen (s [ ts ]) (⟦ s ⟧ Δ ts cs))
⟦ ƛ_ {τ = τ} t ⟧ Δ ts cs = λ Θ ρ a c → comp-backward _ β-ƛ 
                                                    (transport (Comp τ) (≡-sym (subst-rename-lift-subst ρ ts t a)) 
                                                    (⟦ t ⟧ Θ (a ∷ mapSub (rename ρ) ts) (c ∷ renameᶜ ρ cs)))


-- Define reification ⇓ and reflection ⇑
⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(c : Comp σ t) → Normalizable t
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

⇓ Γ Ans c = c
⇓ Γ 𝟙 c = c
⇓ Γ (σ ẋ τ) (c₁ , c₂) with ⇓ Γ σ c₁ | ⇓ Γ τ c₂
... | t₁ , π₁t→t₁ , n₁ | t₂ , π₂t→t₂ , n₂ = (t₁ , t₂) , η-, ‣ ξ-,⋆ π₁t→t₁ π₂t→t₂ , (n₁ , n₂)
⇓ Γ (σ ⇒ τ) {t} c with ⇓ (σ ∷ Γ) τ (c (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))))
... | t' , weaken-t·`ze→t' , nt' = (ƛ t') , η-ƛ ‣ ξ-ƛ⋆ weaken-t·`ze→t' , (ƛ nt')

⇑ Γ Ans (t , ne) = t , ✦ , (‘ ne)
⇑ Γ 𝟙 (t , ne) = ⟨⟩ , η-⟨⟩ ‣ ✦ , ⟨⟩
⇑ Γ (σ ẋ τ) (t , ne) = ⇑ Γ σ (π₁ t , π₁ ne) , ⇑ Γ τ (π₂ t , π₂ ne)
⇑ Γ (σ ⇒ τ) (t , ne) = λ Θ ρ a c → let (a' , a→a' , na') = ⇓ Θ σ {a} c
                                   in comp-backward⋆ τ (ξ-·⋆ ✦ a→a') (⇑ Θ τ ((rename ρ t · a') , (rename-ne ρ ne · na')))


-- reflection for each term in a neutral substitution
⇑ᶜ : (Γ Δ : Cxt)(ts : Sub Γ Δ) → NeutralSub ts → ⟦ Γ ⟧ᶜ ts
⇑ᶜ [] Δ .[] [] = []
⇑ᶜ (σ ∷ Γ) Δ (t ∷ ts) (nt ∷ ns) = ⇑ Δ σ (t , nt) ∷ ⇑ᶜ Γ Δ ts ns


--  evaluate a term to its computability structure
eval : (t : Γ ⊢ σ) → Comp σ t
eval {Γ} {σ} t = transport (Comp σ) (subst-idSub {t = t}) (⟦ t ⟧ Γ idSub (⇑ᶜ Γ Γ idSub idSub-is-neutral))


-- normalization by evaluation
normalize : (t : Γ ⊢ σ) → Normalizable t
normalize {Γ} {σ} t = ⇓ Γ σ (eval t)

-- test terms
test-term : [] ⊢ Ans
test-term = (ƛ (` ze)) · (π₁ (π₂ (yes , ((ƛ (` ze)) · no)) , ⟨⟩))

test-term2 : 𝟙 ∷ [] ⊢ 𝟙 ẋ 𝟙
test-term2 = (` ze) , ⟨⟩

test-term3 : 𝟙 ∷ [] ⊢ Ans ⇒ 𝟙
test-term3 = (ƛ ((ƛ (` su ze)) · no)) · ((ƛ (ƛ (` su ze))) · (` ze)) -- (λx. (λy. x) no) ((λzw. z) u) 