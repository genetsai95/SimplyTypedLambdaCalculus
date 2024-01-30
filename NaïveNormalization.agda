module NaïveNormalization where

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
    ‘‘_ : {a : Γ ⊢ 𝟙} → Neutral Γ 𝟙 a → Normal Γ 𝟙 a
    _,_ : {a : Γ ⊢ σ}{b : Γ ⊢ τ} → Normal Γ σ a → Normal Γ τ b → Normal Γ (σ ẋ τ) (a , b)
    ƛ_ : {t : σ ∷ Γ ⊢ τ} → Normal (σ ∷ Γ) τ t → Normal Γ (σ ⇒ τ) (ƛ t)

Comp : (σ : Type) → Γ ⊢ σ → Set
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t →β* t') × Normal Γ Ans t')
Comp {Γ} 𝟙 t = Σ (Γ ⊢ 𝟙) (λ t' → (t →β* t') × Normal Γ 𝟙 t')
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (t →β* (t' , t'')) × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = Σ (Γ ⊢ σ ⇒ τ) (λ t' → (t →β* t') × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Σ (Θ ⊢ σ) (λ a' → (a →β* a') × (Comp τ (rename ρ t' · a')))))

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
rename-nf ρ (‘‘ x) = ‘‘ rename-ne ρ x
rename-nf ρ (n₁ , n₂) = rename-nf ρ n₁ , rename-nf ρ n₂
rename-nf ρ (ƛ n) = ƛ rename-nf (lift ρ) n

rename-ne ρ (` x) = ` lookupRen x ρ
rename-ne ρ (π₁ n) = π₁ (rename-ne ρ n)
rename-ne ρ (π₂ n) = π₂ (rename-ne ρ n)
rename-ne ρ (n · x) = rename-ne ρ n · rename-nf ρ x

rename-comp : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
rename-comp {σ = Ans} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
rename-comp {σ = 𝟙} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
rename-comp {σ = σ ẋ τ} ρ t (s , s' , t→s,s' , scs , s'cs) = rename ρ s , rename ρ s' , map-rename ρ t→s,s' , rename-comp ρ s scs , rename-comp ρ s' s'cs
rename-comp {σ = σ ⇒ τ} ρ t (t' , t→t' , f) = rename ρ t' , map-rename ρ t→t' , 
                                              λ Θ ρ' s c → let (s' , s→s' , c') = f Θ (concatRen ρ ρ') s c 
                                                           in s' , s→s' , transport (λ y → Comp τ (y · s')) (rename-concatRen≡rename-rename ρ ρ' t') c'

renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) →β* t') × Comp σ t')
⟦ ` x ⟧ Δ ts cs = lookup x ts , β-base , lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , β-base , yes , β-base , yes
⟦ no ⟧ Δ ts cs = no , β-base , no , β-base , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , β-base , ⟨⟩ , β-base , ⟨⟩
⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , map-pair t[ts]→t' s[ts]→s' , t' , s' , map-pair β-base β-base , t'cs , s'cs
⟦ π₁ t ⟧ Δ ts cs = let (t' , t[ts]→t' , t'' , _ , t'→t'',s , t''cs , _ ) = ⟦ t ⟧ Δ ts cs 
                  in t'' , concatβ* (map-π₁ (concatβ* t[ts]→t' t'→t'',s)) (β-step β-π₁ β-base) , t''cs
⟦ π₂ t ⟧ Δ ts cs = let (t' , t[ts]→t' , _ , t'' , t'→s,t'' , _ , t''cs) = ⟦ t ⟧ Δ ts cs 
                  in t'' , concatβ* (map-π₂ (concatβ* t[ts]→t' t'→s,t'')) (β-step β-π₂ β-base) , t''cs
⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'' , t'→t'' , f | s' , s[ts]→s' , s'cs = let (s'' , s'→s'' , c) = f Δ idRen s' s'cs 
                                                                in (t'' · s'') , 
                                                                   map-app (concatβ* t[ts]→t' t'→t'') (concatβ* s[ts]→s' s'→s'') ,
                                                                   transport (λ y → Comp τ (y · s'')) (rename-idRen t'') c
⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                                λ Θ ρ s scs → s , β-base ,
                                              let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                              in t'' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) (concatβ* t[s∷mr-ts]→t' t'→t'')) , nt''
⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                                λ Θ ρ s scs → s , β-base , 
                                              let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs)
                                              in t'' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) (concatβ* t[s∷mr-ts]→t' t'→t'')) , nt''
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                                λ Θ ρ s scs → s , β-base ,
                                              let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs)
                                              in t₁ , t₂ ,
                                                 β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) (concatβ* t[s∷mr-ts]→t' t'→t₁,t₂)) ,
                                                 t₁cs , t₂cs
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (ƛ subst t (ts ↑)) , β-base , 
                                λ Θ ρ s scs → s , β-base ,
                                              let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                              in t'' , concatβ* (β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) β-base)) (concatβ* t[s∷mr-ts]→t' t'→t'') , 
                                                 λ Θ' ρ' s' c → f Θ' ρ' s' c


⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

⇓ Γ Ans c = c
⇓ Γ 𝟙 c = c
⇓ Γ (σ ẋ τ) (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
... | t₁' , t₁→t₁' , nt₁' | t₂' , t₂→t₂' , nt₂' = (t₁' , t₂') , concatβ* t→t₁,t₂ (map-pair t₁→t₁' t₂→t₂') , (nt₁' , nt₂')
⇓ Γ (σ ⇒ τ) (n , t→n , f) = let (z , `ze→z , c) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
                            in {! ⇓ (σ ∷ Γ) τ c  !}
                            -- let (n , nf) = ⇓ (σ ∷ Γ) τ (f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze)))) 
                            -- in (ƛ n) , (ƛ nf)
                            ---
                            -- let (t , tcs) = ⇑ (σ ∷ Γ) σ ((` ze) , (` ze)) 
                            -- in let (n , nf) = ⇓ (σ ∷ Γ) τ (f (σ ∷ Γ) wk t tcs) 
                            --    in (ƛ n) , (ƛ nf)

⇑ Γ Ans (n , ne) = n , β-base , (‘ ne)
⇑ Γ 𝟙 (n , ne) = {!   !} --`nil
⇑ Γ (σ ẋ τ) (n , ne) with ⇑ Γ σ (π₁ n , π₁ ne) | ⇑ Γ τ (π₂ n , π₂ ne)
... | n₁cs | n₂cs = {!   !} --π₁ n , π₂ n , β-base , β-base , n₁cs , n₂cs
⇑ Γ (σ ⇒ τ) (n , ne) = n , β-base , λ Θ ρ s c → let (s' , nf) = ⇓ Θ σ {s} c 
                                                in {! ⇑ Θ τ ((rename ρ n · s') , (rename-ne ρ ne · nf)) !}

----
-- ⇑ Γ Ans (n , ne) = n , n , β-base , (‘ ne)
-- ⇑ Γ 𝟙 _ = ⟨⟩ , `nil
-- ⇑ Γ (σ ẋ τ) (n , ne) with ⇑ Γ σ (π₁ n , π₁ ne) | ⇑ Γ τ (π₂ n , π₂ ne)
-- ... | n₁ , n₁cs | n₂ , n₂cs = (n₁ , n₂) , n₁ , n₂ , β-step β-π₁ β-base , β-step β-π₂ β-base , n₁cs , n₂cs
-- ⇑ Γ (σ ⇒ τ) (n , ne) = n , n , β-base , 
--                        λ Θ ρ s c → let (s' , nf) = ⇓ Θ σ {s} c 
--                                    in {!   !} 


-- module NaïveNormalization where

-- open import STLC

-- data Neutral : (Γ : Cxt)(σ : Type) → Γ ⊢ σ → Set
-- data Normal : (Γ : Cxt)(σ : Type) → Γ ⊢ σ → Set

-- data Neutral where
--     `_ : (x : Γ ∋ σ) → Neutral Γ σ (` x)
--     π₁ : {p : Γ ⊢ σ ẋ τ} → Neutral Γ (σ ẋ τ) p → Neutral Γ σ (π₁ p)
--     π₂ : {p : Γ ⊢ σ ẋ τ} → Neutral Γ (σ ẋ τ) p → Neutral Γ τ (π₂ p)
--     _·_ : {f : Γ ⊢ σ ⇒ τ}{a : Γ ⊢ σ} → Neutral Γ (σ ⇒ τ) f → Normal Γ σ a → Neutral Γ τ (f · a)

-- data Normal where
--     yes : ∀{Γ} → Normal Γ Ans yes
--     no : ∀{Γ} → Normal Γ Ans no
--     ‘_ : {a : Γ ⊢ Ans} → Neutral Γ Ans a → Normal Γ Ans a
--     ⟨⟩ : ∀{Γ} → Normal Γ 𝟙 ⟨⟩
--     _,_ : {a : Γ ⊢ σ}{b : Γ ⊢ τ} → Normal Γ σ a → Normal Γ τ b → Normal Γ (σ ẋ τ) (a , b)
--     ƛ_ : {t : σ ∷ Γ ⊢ τ} → Normal (σ ∷ Γ) τ t → Normal Γ (σ ⇒ τ) (ƛ t)

-- Comp : (σ : Type) → Γ ⊢ σ → Set
-- Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → Normal Γ Ans t' × (t' ≡ t))
-- Comp 𝟙 t = ⊤
-- Comp (σ ẋ τ) t = Comp σ (π₁ t) × Comp τ (π₂ t)
-- Comp {Γ} (σ ⇒ τ) t = (Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Comp τ ((rename ρ t) · a)

-- comp-β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → Comp σ (π₁ (t , s)) → Comp σ t
-- comp-β-π₁ u = {!   !}

-- ⟦_⟧ᶜ : Cxt → Cxt → Set
-- ⟦ Γ ⟧ᶜ Δ = Sub Γ Δ

-- ⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ Δ → Set
-- ⟦ Γ ⟧ˢ ts = ∀{τ} → (x : Γ ∋ τ) → Comp τ (lookup x ts)


-- ext-s : {ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → {t : Δ ⊢ σ} → Comp σ t → ⟦ σ ∷ Γ ⟧ˢ (t ∷ ts)
-- ext-s u s ze = s
-- ext-s u s (su x) = u x

-- rename-nf : (ρ : Ren Γ Δ){t : Γ ⊢ σ} → Normal Γ σ t → Normal Δ σ (rename ρ t)
-- rename-ne : (ρ : Ren Γ Δ){t : Γ ⊢ σ} → Neutral Γ σ t → Neutral Δ σ (rename ρ t)

-- rename-nf ρ yes = yes
-- rename-nf ρ no = no
-- rename-nf ρ (‘ x) = ‘ rename-ne ρ x
-- rename-nf ρ ⟨⟩ = ⟨⟩
-- rename-nf ρ (n₁ , n₂) = rename-nf ρ n₁ , rename-nf ρ n₂
-- rename-nf ρ (ƛ n) = ƛ rename-nf (lift ρ) n

-- rename-ne ρ (` x) = ` lookupRen x ρ
-- rename-ne ρ (π₁ n) = π₁ (rename-ne ρ n)
-- rename-ne ρ (π₂ n) = π₂ (rename-ne ρ n)
-- rename-ne ρ (n · x) = rename-ne ρ n · rename-nf ρ x

-- comp-under-rename : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
-- comp-under-rename {σ = Ans} ρ t (t' , nt' , eq') = rename ρ t' , (rename-nf ρ nt' , cong (rename ρ) eq')
-- comp-under-rename {σ = 𝟙} _ _ _ = `nil
-- comp-under-rename {σ = σ ẋ τ} ρ t (c₁ , c₂) = comp-under-rename ρ (π₁ t) c₁ , comp-under-rename ρ (π₂ t) c₂
-- comp-under-rename {σ = σ ⇒ τ} ρ t c Θ ρ' a u = {!  c ? ? a u  !} --comp-under-rename ρ t c Θ ρ' a u

-- rename-c : Ren Δ Θ → ⟦ Γ ⟧ᶜ Δ → ⟦ Γ ⟧ᶜ Θ
-- rename-c ρ = mapSub (rename ρ)

-- rename-s : {ρ : Ren Δ Θ}{ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (rename-c ρ ts)
-- rename-s u x = {! u x   !}

-- ⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(u : ⟦ Γ ⟧ˢ ts) → Comp σ (subst t ts)
-- ⟦ ` x ⟧ Δ a u = u x
-- ⟦ yes ⟧ Δ a u = yes , (yes , refl)
-- ⟦ no ⟧ Δ a u = no , (no , refl)
-- ⟦ ⟨⟩ ⟧ Δ a u = `nil
-- ⟦ t , s ⟧ Δ a u = {!   !} -- ⟦ t ⟧ Δ a u , ⟦ s ⟧ Δ a u
-- ⟦ π₁ t ⟧ Δ a u = pr₁ (⟦ t ⟧ Δ a u)
-- ⟦ π₂ t ⟧ Δ a u = pr₂ (⟦ t ⟧ Δ a u)
-- ⟦ t · s ⟧ Δ a u = {!   !} -- ⟦ t ⟧ Δ a u Δ (λ x → x) (subst a s) (⟦ s ⟧ Δ a u)
-- ⟦ ƛ t ⟧ Δ a u = λ Θ ρ a' u' → {!   !} -- ⟦ t ⟧ Θ (ext-c (rename-c ρ a) a') (ext-s (rename-s u) u')

-- ⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → ∃[ t' ∶ Γ ⊢ σ ] Normal Γ σ t'
-- ⇑ : (Γ : Cxt)(σ : Type) → ((n' , _) : ∃[ n ∶ Γ ⊢ σ ] Neutral Γ σ n) → Comp σ n'

-- ⇓ Γ Ans (t , p) = t , pr₁ p
-- ⇓ Γ 𝟙 u = ⟨⟩ , ⟨⟩
-- ⇓ Γ (σ ẋ τ) (u , v) with ⇓ Γ σ u | ⇓ Γ τ v
-- ... | (t , nt) | (s , ns) = (t , s) , (nt , ns)
-- ⇓ Γ (σ ⇒ τ) u with ⇓ (σ ∷ Γ) τ (u (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))))
-- ... | (t , nt) = (ƛ t) , (ƛ nt)

-- ⇑ Γ Ans (n , nn) = n , ((‘ nn) , refl)
-- ⇑ Γ 𝟙 n = `nil
-- ⇑ Γ (σ ẋ τ) (n , nn) = ⇑ Γ σ (π₁ n , π₁ nn) , ⇑ Γ τ (π₂ n , π₂ nn)
-- ⇑ Γ (σ ⇒ τ) (n , nn) Θ ρ a u = {!  !} -- ⇑ Θ τ {!   !} -- ((rename ρ n · pr₁ (⇓ Θ σ u)) , {!   !})
  