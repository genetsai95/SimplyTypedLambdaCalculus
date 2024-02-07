module NaïveNormalization-without-η where

open import STLC
open import STLC.Reduction
open import STLC.Normal-without-η

Comp : (σ : Type) → Γ ⊢ σ → Set
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t →β* t') × Normal Γ Ans t')
Comp {Γ} 𝟙 t = Σ (Γ ⊢ 𝟙) (λ t' → (t →β* t') × Normal Γ 𝟙 t')
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ ẋ τ) (λ t' → (t →β* t') × Normal Γ (σ ẋ τ) t') ⊎ Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (t →β* (t' , t'')) × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = 
   -- Σ (σ ∷ Γ ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Comp τ (rename (lift ρ) t' [ a /x])))
   -- Σ (σ ∷ Γ ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Σ (Θ ⊢ σ) (λ a' → (a →β* a') × Comp τ (rename (lift ρ) t' [ a' /x]))))
   Σ (Γ ⊢ σ ⇒ τ) (λ t' → (t →β* t') × Normal Γ (σ ⇒ τ) t') ⊎ Σ (σ ∷ Γ ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Σ (Θ ⊢ σ) (λ a' → (a →β* a') × Comp τ (rename (lift ρ) t' [ a' /x]))))

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

rename-comp : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
rename-comp {σ = Ans} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
rename-comp {σ = 𝟙} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
rename-comp {σ = σ ẋ τ} ρ t (inl (t' , t→t' , nt')) = inl (rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt')
rename-comp {σ = σ ẋ τ} ρ t (inr (s , s' , t→s,s' , scs , s'cs)) = inr (rename ρ s , rename ρ s' , map-rename ρ t→s,s' ▷ map-pair ✦ ✦ , rename-comp ρ s scs , rename-comp ρ s' s'cs)
rename-comp {σ = σ ⇒ τ} ρ t (inl (t' , t→t' , nt')) = inl (rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt')
rename-comp {σ = σ ⇒ τ} ρ t (inr (t' , t→t' , f)) = inr (rename (lift ρ) t' , map-rename ρ t→t' , 
                                                         λ Θ ρ' s c → let (s' , s→s' , s'cs) = f Θ (concatRen ρ ρ') s c 
                                                                      in s' , s→s' ,
                                                                         transport (λ y → Comp τ (y [ s' /x])) 
                                                                                   (   rename (lift (concatRen ρ ρ')) t'
                                                                                    ≡⟨ cong (λ y → rename y t') (≡-sym (concatRen-lift ρ ρ')) ⟩
                                                                                       rename (concatRen (lift ρ) (lift ρ')) t'
                                                                                    ≡⟨ rename-concatRen≡rename-rename (lift ρ) (lift ρ') t' ⟩ 
                                                                                       rename (lift ρ') (rename (lift ρ) t') 
                                                                                    ∎)
                                                                                    s'cs
                                                         )

renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

compNormal : {t : Γ ⊢ σ} → Normal Γ σ t → Comp σ t
compNormal {σ = Ans} {t} nt = t , ✦ , nt
compNormal {σ = 𝟙} {t} nt = t , ✦ , nt
compNormal {σ = σ ẋ τ} {t} nt = inl (t , ✦ , nt)
compNormal {σ = σ ⇒ τ} {t} nt = inl (t , ✦ , nt) 

⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

⇓ Γ Ans cs = cs
⇓ Γ 𝟙 cs = cs
⇓ Γ (σ ẋ τ) (inl cs) = cs
⇓ Γ (σ ẋ τ) (inr (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs)) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
... | n₁ , t₁→n₁ , nf₁ | n₂ , t₂→n₂ , nf₂ = (n₁ , n₂) , t→t₁,t₂ ▷ map-pair t₁→n₁ t₂→n₂ , (nf₁ , nf₂)
⇓ Γ (σ ⇒ τ) (inl cs) = cs
⇓ Γ (σ ⇒ τ) (inr (t' , t→ƛt' , f)) = let (z , `ze→z , zcs) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
                                     in let (t'' , ren-t'[z]→t'' , nt'') = ⇓ (σ ∷ Γ) τ zcs 
                                        in (ƛ t'') , 
                                            t→ƛt' ▷ map-ƛ (same eq ‣ map-/x (rename (lift wk) t') `ze→z ▷ ren-t'[z]→t'') ,
                                           (ƛ nt'')
                                            where
                                             eq : t' ≡ rename (lift wk) t' [ ` ze /x]
                                             eq = ≡-sym ((rename (lift wk) t' [ ` ze /x])
                                                      ≡⟨ cong (λ y → rename (lift wk) y [ ` ze /x]) (≡-sym (subst-idSub {t = t'})) ⟩ 
                                                         (rename (lift wk) (subst t' (idSub ↑)) [ ` ze /x])
                                                      ≡⟨ subst-rename-lift-subst wk idSub t' (` ze) ⟩ 
                                                          subst t' (idSub ↑)
                                                      ≡⟨ subst-idSub {t = t'} ⟩ 
                                                          t'
                                                      ∎)

⇑ Γ Ans (n , ne) = n , ✦ , (‘ ne)
⇑ Γ 𝟙 (n , ne) = n , ✦ , (‘ ne)
⇑ Γ (σ ẋ τ) (n , ne) = inl (n , ✦ , (‘ ne))
⇑ Γ (σ ⇒ τ) (n , ne) = inl (n , ✦ , (‘ ne))

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) →β* t') × Comp σ t')
⟦ ` x ⟧ Δ ts cs = lookup x ts , ✦ , lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , ✦ , yes , ✦ , yes
⟦ no ⟧ Δ ts cs = no , ✦ , no , ✦ , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩ , ✦ , ⟨⟩
⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , map-pair t[ts]→t' s[ts]→s' , inr (t' , s' , ✦ , t'cs , s'cs)
⟦ π₁ t ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs
... | t' , t[ts]→t' , inl (t'' , t'→t'' , (‘ x)) = π₁ t'' , map-π₁ (t[ts]→t' ▷ t'→t'') , compNormal (‘ π₁ x)
... | t' , t[ts]→t' , inl ((t₁ , _)  , t'→t₁,t₂ , (nt₁ , _)) = t₁ , map-π₁ (t[ts]→t' ▷ t'→t₁,t₂) ▷ (β-π₁ ‣ ✦) , compNormal nt₁
... | t' , t[ts]→t' , inr (t'' , _ , t'→t'',s , t''cs , _) = t'' , map-π₁ (t[ts]→t' ▷ t'→t'',s) ▷ (β-π₁ ‣ ✦) , t''cs
⟦ π₂ t ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs
... | t' , t[ts]→t' , inl (t'' , t'→t'' , (‘ x)) = π₂ t'' , map-π₂ (t[ts]→t' ▷ t'→t'') , compNormal (‘ π₂ x)
... | t' , t[ts]→t' , inl ((_ , t₂) , t'→t₁,t₂ , (_ , nt₂)) = t₂ , map-π₂ (t[ts]→t' ▷ t'→t₁,t₂) ▷ (β-π₂ ‣ ✦) , compNormal nt₂
... | t' , t[ts]→t' , inr (_ , t'' , t'→s,t'' , _ , t''cs) = t'' , map-π₂ (t[ts]→t' ▷ t'→s,t'') ▷ (β-π₂ ‣ ✦) , t''cs
⟦ _·_ {σ = σ} {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , inl (t'' , t'→t'' , (‘ x)) | s' , s[ts]→s' , s'cs = let (s'' , s'→s'' , ns'') = ⇓ Δ σ s'cs
                                                                          in (t'' · s'') , map-app (t[ts]→t' ▷ t'→t'') (s[ts]→s' ▷ s'→s'') , compNormal (‘ (x · ns''))
... | t' , t[ts]→t' , inl ((ƛ t'') , t'→ƛt'' , (ƛ nt'')) | s' , s[ts]→s' , s'cs = {!   !}
... | t' , t[ts]→t' , inr x | s' , s[ts]→s' , s'cs = {!   !}
⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = {!   !}
⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = {!   !}
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = {!   !}
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = {!   !}
-- ⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
-- ... | t' , t[ts]→t' , t'' , t'→ƛt'' , f | s' , s[ts]→s' , s'cs = let (s'' , s'→s'' , s''cs) = f Δ idRen s' s'cs 
--                                                                  in (t'' [ s'' /x]) , map-app (t[ts]→t' ▷ t'→ƛt'') (s[ts]→s' ▷ s'→s'') ▷ (β-ƛ ‣ ✦) ,
--                                                                     transport (λ y → Comp τ (y [ s'' /x])) (rename-idRen t'') s''cs
-- ⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
--                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
--                                             in s , ✦ ,  t'' , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
-- ⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
--                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
--                                             in s , ✦ , t'' , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
-- ⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ ,
--                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
--                                             in s , ✦ , t₁ , t₂ , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t₁,t₂ , t₁cs , t₂cs
-- ⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
--                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→ƛt'' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
--                                             in s , ✦ , t'' , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→ƛt'' , λ Θ' ρ' s' c' → f Θ' ρ' s' c'


-- ⇑ˢ : (Γ Δ : Cxt)(ts : Sub Γ Δ) → NeutralSub ts → ⟦ Γ ⟧ˢ ts
-- ⇑ˢ [] Δ [] [] = []
-- ⇑ˢ (σ ∷ Γ) Δ (t ∷ ts) (nt ∷ ns) = ⇑ Δ σ (t , nt) ∷ ⇑ˢ Γ Δ ts ns

-- eval : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Comp σ t')
-- eval {Γ} t = let (t' , t[id]→t' , t'cs) = ⟦ t ⟧ Γ idSub (⇑ˢ Γ Γ idSub idSub-is-neutral) 
--              in t' , transport (λ y → y →β* t') (subst-idSub {t = t}) t[id]→t' , t'cs

-- normalize : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')
-- normalize {Γ} {σ} t = let (t' , t→t' , t'cs) = eval t 
--                        in let (t'' , t'→t'' , nt'') = ⇓ Γ σ t'cs 
--                           in t'' , t→t' ▷ t'→t'' , nt''