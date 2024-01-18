module NaïveNormalization' where

open import STLC

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
    _,_ : {a : Γ ⊢ σ}{b : Γ ⊢ τ} → Normal Γ σ a → Normal Γ τ b → Normal Γ (σ ẋ τ) (a , b)
    ƛ_ : {t : σ ∷ Γ ⊢ τ} → Normal (σ ∷ Γ) τ t → Normal Γ (σ ⇒ τ) (ƛ t)

Comp : (σ : Type) → Γ ⊢ σ → Set
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t →β* t') × Normal Γ Ans t')
Comp {Γ} 𝟙 t = t →β* ⟨⟩
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (π₁ t →β* t') × (π₂ t →β* t'') × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = Σ (Γ ⊢ σ ⇒ τ) (λ t' → (t →β* t') × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Comp τ ((rename ρ t') · a)))

⟦_⟧ᶜ : Cxt → Cxt → Set
⟦ Γ ⟧ᶜ Δ = Sub Γ Δ

_[_] : Γ ⊢ σ → ⟦ Γ ⟧ᶜ Δ → Δ ⊢ σ
t [ ts ] = subst t ts

infix 25 _[_]

data ⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ Δ → Set where
    [] : ∀{Δ} → ⟦ [] ⟧ˢ ([] {Δ})
    _∷_ : ∀{σ} → {t : Δ ⊢ σ}{ts : ⟦ Γ ⟧ᶜ Δ} → Comp σ t → ⟦ Γ ⟧ˢ ts → ⟦ (σ ∷ Γ) ⟧ˢ (t ∷ ts)

lookupˢ : {ts : ⟦ Γ ⟧ᶜ Δ}(x : Γ ∋ σ) → ⟦ Γ ⟧ˢ ts → Comp σ (lookup x ts)
lookupˢ ze (c ∷ _) = c
lookupˢ (su x) (_ ∷ cs) = lookupˢ x cs

mapˢ : (fₜ : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ)(fₛ : ∀{σ} → {t : Δ ⊢ σ} → Comp σ t → Comp σ (fₜ t)) → {ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub fₜ ts)
mapˢ fₜ fₛ [] = []
mapˢ fₜ fₛ (c ∷ cs) = fₛ c ∷ mapˢ fₜ fₛ cs


rename-nf : (ρ : Ren Γ Δ){t : Γ ⊢ σ} → Normal Γ σ t → Normal Δ σ (rename ρ t)
rename-ne : (ρ : Ren Γ Δ){t : Γ ⊢ σ} → Neutral Γ σ t → Neutral Δ σ (rename ρ t)

rename-nf ρ yes = yes
rename-nf ρ no = no
rename-nf ρ (‘ x) = ‘ rename-ne ρ x
rename-nf ρ ⟨⟩ = ⟨⟩
rename-nf ρ (n₁ , n₂) = rename-nf ρ n₁ , rename-nf ρ n₂
rename-nf ρ (ƛ n) = ƛ rename-nf (lift ρ) n

rename-ne ρ (` x) = ` lookupRen x ρ
rename-ne ρ (π₁ n) = π₁ (rename-ne ρ n)
rename-ne ρ (π₂ n) = π₂ (rename-ne ρ n)
rename-ne ρ (n · x) = rename-ne ρ n · rename-nf ρ x

rename-comp : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
rename-comp {σ = Ans} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
rename-comp {σ = 𝟙} ρ t t→⟨⟩ = map-rename ρ t→⟨⟩
rename-comp {σ = σ ẋ τ} ρ t (s , s' , π₁t→s , π₂t→s' , scs , s'cs) = rename ρ s , rename ρ s' , map-rename ρ π₁t→s , map-rename ρ π₂t→s' , rename-comp ρ s scs , rename-comp ρ s' s'cs
rename-comp {σ = σ ⇒ τ} ρ t (t' , t→t' , f) = rename ρ t' , map-rename ρ t→t' , λ Θ ρ' s c → transport (λ y → Comp τ (y · s)) (rename-concatRen≡rename-rename ρ ρ' t') (f Θ (concatRen ρ ρ') s c)

renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) →β* t') × Comp σ t')
⟦ ` x ⟧ Δ ts cs = lookup x ts , β-base , lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , β-base , yes , β-base , yes
⟦ no ⟧ Δ ts cs = no , β-base , no , β-base , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , β-base , β-base
⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , map-pair t[ts]→t' s[ts]→s' , t' , s' , β-step β-π₁ β-base , β-step β-π₂ β-base , t'cs , s'cs
⟦ π₁ t ⟧ Δ ts cs = let (t' , t[ts]→t' , t'' , _ , π₁t'→t'' , _ , t''cs , _ ) = ⟦ t ⟧ Δ ts cs 
                  in t'' , concatβ* (map-π₁ t[ts]→t') π₁t'→t'' , t''cs
⟦ π₂ t ⟧ Δ ts cs = let (t' , t[ts]→t' , _ , t'' , _ , π₂t'→t'' , _ , t''cs) = ⟦ t ⟧ Δ ts cs 
                  in t'' , concatβ* (map-π₂ t[ts]→t') π₂t'→t'' , t''cs
⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'' , t'→t'' , f | s' , s[ts]→s' , s'cs = (t'' · s') , map-app (concatβ* t[ts]→t' t'→t'') s[ts]→s' , transport (λ y → Comp τ (y · s')) (rename-idRen t'') (f Δ idRen s' s'cs)
⟦ ƛ_ {τ = Ans} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                             λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                           in t'' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) (concatβ* t[s∷mr-ts]→t' t'→t'')) , nt''
⟦ ƛ_ {τ = 𝟙} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                          λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , tcs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                        in {!   !} --t'' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) (concatβ* t[s∷mr-ts]→t' t'→t'')) 
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                               λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , π₁t'→t₁ , π₂t'→t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                             in t₁ , t₂ , concatβ* (map-π₁ (β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) β-base))) (concatβ* (map-π₁ t[s∷mr-ts]→t') π₁t'→t₁) 
                                                        , concatβ* (map-π₂ (β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) β-base))) (concatβ* (map-π₂ t[s∷mr-ts]→t') π₂t'→t₂) 
                                                        , t₁cs , t₂cs
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                               λ Θ ρ s scs → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                             in t'' , concatβ* (β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) β-base)) (concatβ* t[s∷mr-ts]→t' t'→t'') , 
                                                λ Θ' ρ' s' c → f Θ' ρ' s' c

⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (λ t' → Neutral Γ σ t')) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Comp σ t)

⇓ Γ Ans (n , t→n , nf) = n , t→n , nf
⇓ Γ 𝟙 {t} x = {!   !}
⇓ Γ (σ ẋ σ₁) c = {!   !}
⇓ Γ (σ ⇒ σ₁) c = {!   !}

⇑ Γ σ c = {!   !}

-- -- ⇓ Γ Ans (t , p) = t , pr₁ p
-- -- ⇓ Γ 𝟙 u = ⟨⟩ , ⟨⟩
-- -- ⇓ Γ (σ ẋ τ) (u , v) with ⇓ Γ σ u | ⇓ Γ τ v
-- -- ... | (t , nt) | (s , ns) = (t , s) , (nt , ns)
-- -- ⇓ Γ (σ ⇒ τ) u with ⇓ (σ ∷ Γ) τ (u (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))))
-- -- ... | (t , nt) = (ƛ t) , (ƛ nt)

-- -- ⇑ Γ Ans (n , nn) = n , ((‘ nn) , refl)
-- -- ⇑ Γ 𝟙 n = `nil
-- -- ⇑ Γ (σ ẋ τ) (n , nn) = ⇑ Γ σ (π₁ n , π₁ nn) , ⇑ Γ τ (π₂ n , π₂ nn)
-- -- ⇑ Γ (σ ⇒ τ) (n , nn) Θ ρ a u = {!  !} -- ⇑ Θ τ {!   !} -- ((rename ρ n · pr₁ (⇓ Θ σ u)) , {!   !})
 