module NaïveNormalization-v2 where

open import STLC
open import STLC.Conversion
open import STLC.Normal

Comp : (σ : Type) → Γ ⊢ σ → Set
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t ⟶⋆ t') × Normal Γ Ans t')
Comp {Γ} 𝟙 t = Σ (Γ ⊢ 𝟙) (λ t' → (t ⟶⋆ t') × Normal Γ 𝟙 t')
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (π₁ t ⟶⋆ t') × (π₂ t ⟶⋆ t'') × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) 
                     → Comp τ (rename ρ t · a))

-- substitute variables in Γ with terms under context Δ
⟦_⟧ᶜ : Cxt → Cxt → Set
⟦ Γ ⟧ᶜ Δ = Sub Γ Δ

_[_] : Γ ⊢ σ → ⟦ Γ ⟧ᶜ Δ → Δ ⊢ σ
t [ ts ] = subst t ts

infix 25 _[_]

-- a list of computability structures corresponding to each term in a given substution
data ⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ Δ → Set where
    [] : ∀{Δ} → ⟦ [] ⟧ˢ ([] {Δ})
    _∷_ : ∀{σ} → {t : Δ ⊢ σ}{ts : ⟦ Γ ⟧ᶜ Δ} → Comp σ t → ⟦ Γ ⟧ˢ ts → ⟦ (σ ∷ Γ) ⟧ˢ (t ∷ ts)

lookupˢ : {ts : ⟦ Γ ⟧ᶜ Δ}(x : Γ ∋ σ) → ⟦ Γ ⟧ˢ ts → Comp σ (lookup x ts)
lookupˢ ze (c ∷ _) = c
lookupˢ (su x) (_ ∷ cs) = lookupˢ x cs

mapˢ : (fₜ : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ)(fₛ : ∀{σ} → {t : Δ ⊢ σ} → Comp σ t → Comp σ (fₜ t)) → {ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub fₜ ts)
mapˢ fₜ fₛ [] = []
mapˢ fₜ fₛ (c ∷ cs) = fₛ c ∷ mapˢ fₜ fₛ cs

-- renaming preserves computability structures
rename-comp : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
rename-comp {σ = Ans} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
rename-comp {σ = 𝟙} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
rename-comp {σ = σ ẋ τ} ρ t (s , s' , π₁t→s , π₂t→s' , scs , s'cs) = rename ρ s , rename ρ s' , map-rename ρ π₁t→s , map-rename ρ π₂t→s' , rename-comp ρ s scs , rename-comp ρ s' s'cs
rename-comp {σ = σ ⇒ τ} ρ t f = λ Θ ρ' s c → transport (λ y → Comp τ (y · s)) (rename-concatRen≡rename-rename ρ ρ' t) (f Θ (concatRen ρ ρ') s c)

renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

-- mapping a substition (with the Comp for each term) to the Comp for each term after substitution
⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : Sub Γ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) ⟶⋆ t') × Comp σ t')
⟦ ` x ⟧ Δ ts cs = lookup x ts , ✦ , lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , ✦ , yes , ✦ , yes
⟦ no ⟧ Δ ts cs = no , ✦ , no , ✦ , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩ , ✦ , ⟨⟩
⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , map-pair t[ts]→t' s[ts]→s' , t' , s' , β-π₁ ‣ ✦ , β-π₂ ‣ ✦ , t'cs , s'cs
⟦ π₁ t ⟧ Δ ts cs = let (t' , t[ts]→t' , t'' , _ , π₁t'→t'' , _ , t''cs , _ ) = ⟦ t ⟧ Δ ts cs 
                  in t'' , map-π₁ t[ts]→t' ▷ π₁t'→t'' , t''cs
⟦ π₂ t ⟧ Δ ts cs = let (t' , t[ts]→t' , _ , t'' , _ , π₂t'→t'' , _ , t''cs) = ⟦ t ⟧ Δ ts cs 
                  in t'' , map-π₂ t[ts]→t' ▷ π₂t'→t'' , t''cs
⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , f | s' , s[ts]→s' , s'cs = (t' · s') , 
                                                  map-app t[ts]→t' s[ts]→s' ,
                                                  transport (λ y → Comp τ (y · s')) (rename-idRen t') (f Δ idRen s' s'cs)
⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = ((ƛ t) [ ts ]) , ✦ ,
                                 λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                               in t'' , β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = ((ƛ t) [ ts ]) , ✦ ,
                                λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs)
                                              in t'' , β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ ,
                                λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , π₁t'→t₁ , π₂t'→t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs)
                                              in t₁ , t₂ ,
                                                 map-π₁ (β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t') ▷ π₁t'→t₁ ,
                                                 map-π₂ (β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t') ▷ π₂t'→t₂ ,
                                                 t₁cs , t₂cs
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ ,
                                λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                              in λ Θ' ρ' s' c → {!   !}
                                                --  t' , (β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ ✦) ▷ t[s∷mr-ts]→t' ,
                                                --  λ Θ' ρ' s' c → f Θ' ρ' s' c


-- ⇓ generates normal form from Comp
-- ⇑ generates Comp from neutral forms
⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

⇓ Γ Ans c = c
⇓ Γ 𝟙 c = c
⇓ Γ (σ ẋ τ) (t₁ , t₂ , π₁t→t₁ , π₂t→t₂ , t₁cs , t₂cs) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
... | t₁' , t₁→t₁' , nt₁' | t₂' , t₂→t₂' , nt₂' = (t₁' , t₂') , η-pair ‣ map-pair (π₁t→t₁ ▷ t₁→t₁') (π₂t→t₂ ▷ t₂→t₂') , (nt₁' , nt₂')
⇓ Γ (σ ⇒ τ) f = let (t' , wk-n·ze→t' , nt') = ⇓ (σ ∷ Γ) τ (f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))))
                in (ƛ t') , η-ƛ ‣ map-ƛ wk-n·ze→t' , (ƛ nt')

⇑ Γ Ans (n , ne) = n , ✦ , (‘ ne)
⇑ Γ 𝟙 (n , ne) = n , ✦ , (‘‘ ne)
⇑ Γ (σ ẋ τ) (n , ne) = π₁ n , π₂ n , ✦ , ✦ , ⇑ Γ σ (π₁ n , π₁ ne) , ⇑ Γ τ (π₂ n , π₂ ne)
⇑ Γ (σ ⇒ τ) (n , ne) = λ Θ ρ s c → ⇑ Θ τ ((rename ρ n · s) , {!   !})
                                 --   let (s' , s→s' , ns') = ⇓ Θ σ {s} c 
                                 --   in s' , s→s' , ⇑ Θ τ ((rename ρ n · s') , (rename-ne ρ ne · ns'))

⇑ˢ : (Γ Δ : Cxt)(ts : Sub Γ Δ) → NeutralSub ts → ⟦ Γ ⟧ˢ ts
⇑ˢ [] Δ [] [] = []
⇑ˢ (σ ∷ Γ) Δ (t ∷ ts) (nt ∷ ns) = ⇑ Δ σ (t , nt) ∷ ⇑ˢ Γ Δ ts ns

-- evaluate the computability structure for each term
eval : (t : Γ ⊢ σ) → Comp σ t -- Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Comp σ t')
eval {Γ} t = {! ⟦ t ⟧ Γ idSub (⇑ˢ Γ Γ idSub idSub-is-neutral)   !}
            --  let (t' , t[id]→t' , t'cs) = ⟦ t ⟧ Γ idSub (⇑ˢ Γ Γ idSub idSub-is-neutral) 
            --  in t' , transport (λ y → y ⟶⋆ t') (subst-idSub {t = t}) t[id]→t' , t'cs

-- normalization by first evaluate a term to its Comp and extract normal form from it
-- normalize : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
-- normalize {Γ} {σ} t = let (t' , t→t' , t'cs) = eval t 
--                        in let (t'' , t'→t'' , nt'') = ⇓ Γ σ t'cs 
--                           in t'' , t→t' ▷ t'→t'' , nt''

-- test : [] ⊢ Ans
-- test = π₁ (((ƛ (` ze)) · yes) , no)

-- test' : (𝟙 ẋ Ans) ∷ [] ⊢ Ans
-- test' = π₂ (π₁ (π₂ (⟨⟩ , (` ze)) , no))


_ : {A : Set} → {f : ⊤ → A} → (λ x → f `nil) ≡ f
_ = refl