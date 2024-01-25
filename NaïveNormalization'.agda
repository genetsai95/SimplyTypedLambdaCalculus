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
Comp {Γ} 𝟙 t = t →β* ⟨⟩ -- ⊤
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (t →β* (t' , t'')) × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = Σ (σ ∷ Γ ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Σ (Θ ⊢ τ) (λ a' → ((rename ρ (ƛ t') · a) →β* a') × Comp τ a')))

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
rename-comp {σ = 𝟙} ρ t t→⟨⟩ = map-rename ρ t→⟨⟩ -- `nil
rename-comp {σ = σ ẋ τ} ρ t (s , s' , t→s,s' , scs , s'cs) = rename ρ s , rename ρ s' , concatβ* (map-rename ρ t→s,s') (map-pair β-base β-base) , rename-comp ρ s scs , rename-comp ρ s' s'cs
rename-comp {σ = σ ⇒ τ} ρ t (t' , t→t' , f) = rename (lift ρ) t' , map-rename ρ t→t' , 
                                              λ Θ ρ' s c → let (s' , ren-t'·s→s' , s'cs) = f Θ (concatRen ρ ρ') s c 
                                                           in s' , β-step (β-refl (cong (λ y → (ƛ y) · s) (rename (lift ρ') (rename (lift ρ) t') 
                                                                                                           ≡⟨ ≡-sym (rename-concatRen≡rename-rename (lift ρ) (lift ρ') t') ⟩ rename (concatRen (lift ρ) (lift ρ')) t' 
                                                                                                           ≡⟨ cong (λ y → rename y t') (concatRen-lift ρ ρ') ⟩ rename (lift (concatRen ρ ρ')) t' ∎))) ren-t'·s→s' ,
                                                              s'cs

renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) →β* t') × Comp σ t')
⟦ ` x ⟧ Δ ts cs = lookup x ts , β-base , lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , β-base , yes , β-base , yes
⟦ no ⟧ Δ ts cs = no , β-base , no , β-base , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , β-base , β-base
⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , map-pair t[ts]→t' s[ts]→s' , t' , s' , β-base , t'cs , s'cs
⟦ π₁ t ⟧ Δ ts cs = let (t' , t[ts]→t' , t'' , _ , t'→t'',s , t''cs , _ ) = ⟦ t ⟧ Δ ts cs 
                   in t'' , concatβ* (map-π₁ (concatβ* t[ts]→t' t'→t'',s)) (β-step β-π₁ β-base) , t''cs
⟦ π₂ t ⟧ Δ ts cs = let (t' , t[ts]→t' , _ , t'' , t'→s,t'' , _ , t''cs) = ⟦ t ⟧ Δ ts cs 
                   in t'' , concatβ* (map-π₂ (concatβ* t[ts]→t' t'→s,t'')) (β-step β-π₂ β-base) , t''cs
⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'' , t'→ƛt'' , f | s' , s[ts]→s' , s'cs = let (u , ƛ-ren-id-t''·s'→u , ucs) = f Δ idRen s' s'cs 
                                                                 in u , concatβ* (map-app (concatβ* t[ts]→t' 
                                                                                                    (concatβ* t'→ƛt'' 
                                                                                                             (β-step (β-refl (cong ƛ_ (≡-sym (rename-idRen t'')))) β-base))) 
                                                                                           s[ts]→s') 
                                                                                  ƛ-ren-id-t''·s'→u ,
                                                                    ucs
⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = ((ƛ t) [ ts ]) , β-base , (t [ (ts ↑) ]) , β-base , 
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in t' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t') , 
                                               t'' , t'→t'' , nt''
⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = ((ƛ t) [ ts ]) , β-base , (t [ (ts ↑) ]) , β-base , 
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'→⟨⟩) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in t' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t') , t'→⟨⟩
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (t [ (ts ↑) ]) , β-base ,
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in t' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t') ,
                                               t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , β-base , (t [ (ts ↑) ]) , β-base , 
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→ƛt'' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in t' , β-step β-ƛ (β-step (β-refl (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t') , 
                                               t'' , t'→ƛt'' , λ Θ' ρ' s' c' → f Θ' ρ' s' c'


-- ⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')
-- ⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

-- ⇓ Γ Ans cs = cs
-- ⇓ Γ 𝟙 cs = ⟨⟩ , cs , ⟨⟩
-- ⇓ Γ (σ ẋ τ) (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
-- ... | t₁' , t₁→t₁' , nt₁' | t₂' , t₂→t₂' , nt₂' = (t₁' , t₂') , concatβ* t→t₁,t₂ (map-pair t₁→t₁' t₂→t₂') , (nt₁' , nt₂')
-- ⇓ Γ (σ ⇒ τ) (t' , t→t' , f) = let (s , `ze→s , t'cs) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
--                               in let (n , wk-t'→n , nf) = ⇓ (σ ∷ Γ) τ t'cs 
--                                  in (ƛ n) , concatβ* t→t' (β-step (β-refl (≡-sym {! weaken  !})) {!   !}) , (ƛ nf)

-- ⇑ Γ σ (n , ne) = {!   !}


----------
-- ⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (Normal Γ σ)
-- ⇑ : (Γ : Cxt)(σ : Type) → Σ (Γ ⊢ σ) (Neutral Γ σ) → Σ (Γ ⊢ σ) (Comp σ)


-- ⇓ Γ Ans (n , _ , nf) = n , nf
-- ⇓ Γ 𝟙 {t} _ = ⟨⟩ , ⟨⟩
-- ⇓ Γ (σ ẋ τ) (t₁ , t₂ , π₁t→t₁ , π₂t→t₂ , t₁cs , t₂cs) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
-- ... | t₁' , nt₁' | t₂' , nt₂' = (t₁' , t₂') , (nt₁' , nt₂')
-- ⇓ Γ (σ ⇒ τ) (n , t→n , f) = let (t , tcs) = ⇑ (σ ∷ Γ) σ ((` ze) , (` ze)) 
--                             in let (_ , _ , t'cs) = f (σ ∷ Γ) wk t tcs 
--                                in let (n , nf) = ⇓ (σ ∷ Γ) τ t'cs 
--                                   in (ƛ n) , (ƛ nf)

-- ⇑ Γ Ans (n , ne) = n , n , β-base , (‘ ne)
-- ⇑ Γ 𝟙 _ = ⟨⟩ , `nil
-- ⇑ Γ (σ ẋ τ) (n , ne) with ⇑ Γ σ (π₁ n , π₁ ne) | ⇑ Γ τ (π₂ n , π₂ ne)
-- ... | n₁ , n₁cs | n₂ , n₂cs = (n₁ , n₂) , n₁ , n₂ , β-step β-π₁ β-base , β-step β-π₂ β-base , n₁cs , n₂cs
-- ⇑ Γ (σ ⇒ τ) (n , ne) = n , n , β-base , 
--                        λ Θ ρ s c → let (s' , nf) = ⇓ Θ σ {s} c 
--                                    in {! pr₂ (⇑ Θ τ ?) !} 
