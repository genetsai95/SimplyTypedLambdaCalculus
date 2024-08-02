module NaïveNormalization' where

open import STLC
open import STLC.Conversion
open import STLC.Normal

Comp : (σ : Type) → Γ ⊢ σ → Set
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t ⟶⋆ t') × Normal Γ Ans t')
Comp {Γ} 𝟙 t = Σ (Γ ⊢ 𝟙) (λ t' → (t ⟶⋆ t') × Normal Γ 𝟙 t')
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (t ⟶⋆ (t' , t'')) × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = 
   -- Σ (σ ∷ Γ ⊢ τ) (λ t' → (t ⟶⋆ (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Comp τ (rename (lift ρ) t' [ a /x])))
   Σ (σ ∷ Γ ⊢ τ) (λ t' → (t ⟶⋆ (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Σ (Θ ⊢ σ) (λ a' → (a ⟶⋆ a') × Comp τ (rename (lift ρ) t' [ a' /x]))))

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
rename-comp {σ = Ans} ρ t (t' , t→t' , nt') = rename ρ t' , ξ-rename⋆ ρ t→t' , rename-nf ρ nt'
rename-comp {σ = 𝟙} ρ t (t' , t→t' , nt') = rename ρ t' , ξ-rename⋆ ρ t→t' , rename-nf ρ nt'
rename-comp {σ = σ ẋ τ} ρ t (s , s' , t→s,s' , scs , s'cs) = rename ρ s , rename ρ s' , ξ-rename⋆ ρ t→s,s' ▷ ξ-,⋆ ✦ ✦ , rename-comp ρ s scs , rename-comp ρ s' s'cs
rename-comp {σ = σ ⇒ τ} ρ t (t' , t→t' , f) = rename (lift ρ) t' , ξ-rename⋆ ρ t→t' , 
                                              λ Θ ρ' s c → let (s' , s→s' , s'cs) = f Θ (concatRen ρ ρ') s c 
                                                           in s' , s→s' ,
                                                              transport (λ y → Comp τ (y [ s' /x])) 
                                                                        (rename (lift (concatRen ρ ρ')) t'
                                                                        ≡⟨ cong (λ y → rename y t') (≡-sym (concatRen-lift ρ ρ')) ⟩
                                                                           rename (concatRen (lift ρ) (lift ρ')) t'
                                                                        ≡⟨ rename-concatRen≡rename-rename (lift ρ) (lift ρ') t' ⟩ 
                                                                           rename (lift ρ') (rename (lift ρ) t') 
                                                                        ∎)
                                                                        s'cs

renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) ⟶⋆ t') × Comp σ t')
⟦ ` x ⟧ Δ ts cs = lookup x ts , ✦ , lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , ✦ , yes , ✦ , yes
⟦ no ⟧ Δ ts cs = no , ✦ , no , ✦ , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩ , ✦ , ⟨⟩ --⟨⟩ , ✦ , `nil
⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , ξ-,⋆ t[ts]→t' s[ts]→s' , t' , s' , ✦ , t'cs , s'cs
⟦ π₁ t ⟧ Δ ts cs = let (t' , t[ts]→t' , t'' , _ , t'→t'',s , t''cs , _ ) = ⟦ t ⟧ Δ ts cs 
                   in t'' , ξ-π₁⋆ (t[ts]→t' ▷ t'→t'',s) ▷ (β-π₁ ‣ ✦) , t''cs
⟦ π₂ t ⟧ Δ ts cs = let (t' , t[ts]→t' , _ , t'' , t'→s,t'' , _ , t''cs) = ⟦ t ⟧ Δ ts cs 
                   in t'' , ξ-π₂⋆ (t[ts]→t' ▷ t'→s,t'') ▷ (β-π₂ ‣ ✦) , t''cs
⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'' , t'→ƛt'' , f | s' , s[ts]→s' , s'cs = let (s'' , s'→s'' , s''cs) = f Δ idRen s' s'cs 
                                                                 in (t'' [ s'' /x]) , ξ-·⋆ (t[ts]→t' ▷ t'→ƛt'') (s[ts]→s' ▷ s'→s'') ▷ (β-ƛ ‣ ✦) ,
                                                                    transport (λ y → Comp τ (y [ s'' /x])) (rename-idRen t'') s''cs
⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in s , ✦ ,  t'' , ≡⟶⋆ (≡-sym (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t' ▷ t'→t'' , nt''
⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in s , ✦ , t'' , ≡⟶⋆ (≡-sym (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t' ▷ t'→t'' , nt''
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ ,
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in s , ✦ , t₁ , t₂ , ≡⟶⋆ (≡-sym (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t' ▷ t'→t₁,t₂ , t₁cs , t₂cs
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
                                λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→ƛt'' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
                                            in s , ✦ , t'' , ≡⟶⋆ (≡-sym (subst-rename-lift-subst ρ ts t s)) t[s∷mr-ts]→t' ▷ t'→ƛt'' , λ Θ' ρ' s' c' → f Θ' ρ' s' c'


⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

⇓ Γ Ans cs = cs
⇓ Γ 𝟙 {t} cs = cs
⇓ Γ (σ ẋ τ) (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
... | n₁ , t₁→n₁ , nf₁ | n₂ , t₂→n₂ , nf₂ = (n₁ , n₂) , t→t₁,t₂ ▷ ξ-,⋆ t₁→n₁ t₂→n₂ , (nf₁ , nf₂)
⇓ Γ (σ ⇒ τ) (t' , t→ƛt' , f) = let (z , `ze→z , zcs) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
                               in let (t'' , ren-t'[z]→t'' , nt'') = ⇓ (σ ∷ Γ) τ zcs 
                                  in (ƛ t'') , t→ƛt' ▷ (η-ƛ ‣ ξ-ƛ⋆ ((ξ-·⋆ ✦ `ze→z ▷ (β-ƛ ‣ ✦)) ▷ ren-t'[z]→t'')) , (ƛ nt'')

⇑ Γ Ans (n , ne) = n , ✦ , (‘ ne)
⇑ Γ 𝟙 (n , ne) = ⟨⟩ , η-⟨⟩ ‣ ✦ , ⟨⟩
⇑ Γ (σ ẋ τ) (n , ne) = π₁ n , π₂ n , η-, ‣ ✦ , ⇑ Γ σ (π₁ n , π₁ ne) , ⇑ Γ τ (π₂ n , π₂ ne)
⇑ Γ (σ ⇒ τ) (n , ne) = (weaken {τ = σ} n · (` ze)) , η-ƛ ‣ ✦ ,
                        λ Θ ρ s c → let (s' , s→s' , nf) = ⇓ Θ σ c 
                                    in s' , s→s' , transport (λ y → Comp τ y) eq (⇑ Θ τ ((rename ρ n · s') , (rename-ne ρ ne · nf)))
                                       where
                                          eq : ∀{Γ Δ σ τ} → {ρ : Ren Γ Δ}{t : Γ ⊢ σ ⇒ τ}{s : Δ ⊢ σ} → (rename ρ t · s) ≡ (rename (lift ρ) (weaken t · (` ze)) [ s /x])
                                          eq {ρ = ρ} {t} {s} = ≡-sym (rename (lift ρ) (weaken t · (` ze)) [ s /x]
                                                                  ≡⟨ refl ⟩ 
                                                                     (rename (lift ρ) (weaken t) [ s /x]) · s
                                                                  ≡⟨ cong (λ y → (y [ s /x]) · s) (rename-lift-weaken≡weaken-rename ρ t) ⟩ 
                                                                    ((weaken (rename ρ t) [ s /x]) · s) 
                                                                  ≡⟨ cong (λ y → y · s) (subst-weaken-idSub (rename ρ t) {s}) ⟩ 
                                                                      rename ρ t · s
                                                                  ∎)

⇑ˢ : (Γ Δ : Cxt)(ts : Sub Γ Δ) → NeutralSub ts → ⟦ Γ ⟧ˢ ts
⇑ˢ [] Δ [] [] = []
⇑ˢ (σ ∷ Γ) Δ (t ∷ ts) (nt ∷ ns) = ⇑ Δ σ (t , nt) ∷ ⇑ˢ Γ Δ ts ns

eval : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Comp σ t')
eval {Γ} t = let (t' , t[id]→t' , t'cs) = ⟦ t ⟧ Γ idSub (⇑ˢ Γ Γ idSub idSub-is-neutral) 
             in t' , transport (λ y → y ⟶⋆ t') (subst-idSub {t = t}) t[id]→t' , t'cs

normalize : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
normalize {Γ} {σ} t = let (t' , t→t' , t'cs) = eval t 
                       in let (t'' , t'→t'' , nt'') = ⇓ Γ σ t'cs 
                          in t'' , t→t' ▷ t'→t'' , nt''