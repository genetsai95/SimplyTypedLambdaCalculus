module HereditaryNormalization where

open import STLC
open import STLC.Conversion
open import STLC.Normal

Comp : (σ : Type) → Γ ⊢ σ → Set
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t ⟶⋆ t') × Normal Γ Ans t')
Comp {Γ} 𝟙 t = Σ (Γ ⊢ 𝟙) (λ t' → (t ⟶⋆ t') × Normal Γ 𝟙 t')
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (t ⟶⋆ (t' , t'')) × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = 
   Σ (σ ∷ Γ ⊢ τ) (λ t' → (t ⟶⋆ (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Comp τ (rename (lift ρ) t' [ a /x])))
   -- Σ (σ ∷ Γ ⊢ τ) (λ t' → (t ⟶⋆ (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Σ (Θ ⊢ σ) (λ a' → (a ⟶⋆ a') × Comp τ (rename (lift ρ) t' [ a' /x]))))

-- Shift computability structure by βη-conversion
comp-backward : (σ : Type){t t' : Γ ⊢ σ} → t ⟶ t' → Comp σ t' → Comp σ t
comp-backward Ans t→t' (t'' , t'→t'' , nt'') = t'' , t→t' ‣ t'→t'' , nt''
comp-backward 𝟙 t→t' (t'' , t'→t'' , nt'') = t'' , t→t' ‣ t'→t'' , nt''
comp-backward (σ ẋ τ) t→t' (t'₁ , t'₂ , t'→t'₁,t'₂ , ct'₁ , ct'₂) = t'₁ , t'₂ , t→t' ‣ t'→t'₁,t'₂ , ct'₁ , ct'₂
comp-backward (σ ⇒ τ) t→t' (t'' , t→ƛt'' , f) = t'' , t→t' ‣ t→ƛt'' , f

comp-backward⋆ : (σ : Type){t t' : Γ ⊢ σ} → t ⟶⋆ t' → Comp σ t' → Comp σ t
comp-backward⋆ σ ✦ c = c
comp-backward⋆ σ (t→u ‣ u→*t') c = comp-backward σ t→u (comp-backward⋆ σ u→*t' c)

⟦_⟧ᶜ : Cxt → Cxt → Set
⟦ Γ ⟧ᶜ Δ = Sub Γ Δ

_[_] : Γ ⊢ σ → ⟦ Γ ⟧ᶜ Δ → Δ ⊢ σ
t [ ts ] = subst t ts

infix 35 _[_]

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
                                              λ Θ ρ' s c → transport (λ y → Comp τ (y [ s /x]))
                                                                     (rename (lift (concatRen ρ ρ')) t' 
                                                                     ≡⟨ cong (λ y → rename y t') (≡-sym (concatRen-lift ρ ρ')) ⟩
                                                                      rename (concatRen (lift ρ) (lift ρ')) t' 
                                                                     ≡⟨ rename-concatRen≡rename-rename (lift ρ) (lift ρ') t' ⟩
                                                                      rename (lift ρ') (rename (lift ρ) t')
                                                                     ∎)
                                                                     (f Θ (concatRen ρ ρ') s c)
                                                        --    let (s' , s→s' , s'cs) = f Θ (concatRen ρ ρ') s c 
                                                        --    in s' , s→s' ,
                                                        --       transport (λ y → Comp τ (y [ s' /x])) 
                                                        --                 (rename (lift (concatRen ρ ρ')) t'
                                                        --                 ≡⟨ cong (λ y → rename y t') (≡-sym (concatRen-lift ρ ρ')) ⟩
                                                        --                    rename (concatRen (lift ρ) (lift ρ')) t'
                                                        --                 ≡⟨ rename-concatRen≡rename-rename (lift ρ) (lift ρ') t' ⟩ 
                                                        --                    rename (lift ρ') (rename (lift ρ) t') 
                                                        --                 ∎)
                                                        --                 s'cs

renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Comp σ (t [ ts ])
⟦ ` x ⟧ Δ ts cs = lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , ✦ , yes
⟦ no ⟧ Δ ts cs = no , ✦ , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩
⟦ t , s ⟧ Δ ts cs = t [ ts ] , s [ ts ] , ✦ , ⟦ t ⟧ Δ ts cs , ⟦ s ⟧ Δ ts cs 
⟦ π₁ t ⟧ Δ ts cs = let (t₁ , t₂ , t[ts]→t₁,t₂ , c₁ , c₂) = ⟦ t ⟧ Δ ts cs 
                   in comp-backward⋆ _ (ξ-π₁⋆ t[ts]→t₁,t₂ ▷ (β-π₁ ‣ ✦)) c₁
⟦ π₂ t ⟧ Δ ts cs = let (t₁ , t₂ , t[ts]→t₁,t₂ , c₁ , c₂) = ⟦ t ⟧ Δ ts cs 
                   in comp-backward⋆ _ (ξ-π₂⋆ t[ts]→t₁,t₂ ▷ (β-π₂ ‣ ✦)) c₂
⟦ t · s ⟧ Δ ts cs = let (t' , t→ƛt' , f) = ⟦ t ⟧ Δ ts cs 
                    in comp-backward⋆ _ (ξ-·⋆ t→ƛt' ✦ ▷ (β-ƛ ‣ ✦)) (transport (λ y → Comp _ (y [ s [ ts ] /x]))
                                                                              (rename-idRen t')
                                                                              (f Δ idRen (s [ ts ]) (⟦ s ⟧ Δ ts cs)))
⟦ ƛ_ {σ = σ} t ⟧ Δ ts cs = t [ ts ↑ ] , ✦ , λ Θ ρ a c → transport (Comp _)
                                                                 (≡-sym (subst-rename-lift-subst ρ ts t a))
                                                                 (⟦ t ⟧ Θ (a ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs))

⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

⇓ Γ Ans cs = cs
⇓ Γ 𝟙 cs = cs
⇓ Γ (σ ẋ τ) (t₁ , t₂ , t→t₁,t₂ , c₁ , c₂) with ⇓ Γ σ c₁ | ⇓ Γ τ c₂
... | t₁' , t₁→t₁' , nt₁' | t₂' , t₂→t₂' , nt₂' = (t₁' , t₂') , t→t₁,t₂ ▷ ξ-,⋆ t₁→t₁' t₂→t₂' , (nt₁' , nt₂')
⇓ Γ (σ ⇒ τ) (t' , t→ƛt' , f) = let (t'' , wk-t'[ze]→t'' , nt'') = ⇓ (σ ∷ Γ) τ (f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))))
                               in (ƛ t'') , t→ƛt' ▷ ξ-ƛ⋆ (transport (_⟶⋆ t'') eq wk-t'[ze]→t'') , (ƛ nt'')
    where
        eqv : ∀{σ'} → (x : σ ∷ Γ ∋ σ') → rename (lift wk) (` x) [ (` ze) /x] ≡ subst (` x) idSub
        eqv ze = refl
        eqv (su x) = lookup (lookupRen x (mapRen su wk)) ((` ze) ∷ idSub)
                   ≡⟨ cong (λ y → lookup y ((` ze) ∷ idSub)) (lookupRen-map su x refl) ⟩ 
                     lookup (su (lookupRen x wk)) ((` ze) ∷ idSub)
                   ≡⟨ refl ⟩
                    lookup (lookupRen x (mapRen su idRen)) idSub
                   ≡⟨ cong (λ y → lookup y idSub) (lookupRen-map su x refl) ⟩
                    lookup (su (lookupRen x idRen)) idSub
                   ≡⟨ cong (λ y → lookup (su y) idSub) (lookupRen-idRen x) ⟩
                    lookup (su x) idSub
                   ≡⟨ refl ⟩
                    subst (` su x) idSub
                   ∎
        
        eq : rename (lift wk) t' [ (` ze) /x] ≡ t'
        eq = rename (lift wk) t' [ (` ze) /x]
           ≡⟨ sr-s-eq eqv t' ⟩
            subst t' idSub
           ≡⟨ subst-idSub {t = t'} ⟩
            t'
           ∎

⇑ Γ Ans (t , nt) = t , ✦ , (‘ nt)
⇑ Γ 𝟙 (t , nt) = ⟨⟩ , η-⟨⟩ ‣ ✦ , ⟨⟩
⇑ Γ (σ ẋ τ) (t , nt) = π₁ t , π₂ t , η-, ‣ ✦ , ⇑ Γ σ (π₁ t , π₁ nt) , ⇑ Γ τ (π₂ t , π₂ nt)
⇑ Γ (σ ⇒ τ) (t , nt) = (weaken {τ = σ} t · (` ze)) , η-ƛ ‣ ✦ , 
                       λ Θ ρ a c → let (a' , a→a' , na') = ⇓ Θ σ c 
                                   in comp-backward⋆ _ (ξ-·⋆ ✦ a→a')
                                                     (transport (Comp τ) (app-term-≡ (≡-sym (eq ρ a)) refl) (⇑ Θ τ ((rename ρ t · a') , (rename-ne ρ nt · na'))))
    where
        eq : ∀{σ'} → (ρ : Ren Γ Θ)(a : Θ ⊢ σ') → rename (lift ρ) (weaken t) [ a /x] ≡ rename ρ t
        eq ρ a = rename (lift ρ) (weaken t) [ a /x]
               ≡⟨ cong (_[ a /x]) (rename-lift-weaken≡weaken-rename ρ t) ⟩
                weaken (rename ρ t) [ a /x]
               ≡⟨ subst-weaken-idSub (rename ρ t) {a} ⟩
                rename ρ t
               ∎

⇑ˢ : (Γ Δ : Cxt)(ts : Sub Γ Δ) → NeutralSub ts → ⟦ Γ ⟧ˢ ts
⇑ˢ [] Δ [] [] = []
⇑ˢ (σ ∷ Γ) Δ (t ∷ ts) (nt ∷ ns) = ⇑ Δ σ (t , nt) ∷ ⇑ˢ Γ Δ ts ns

eval : (t : Γ ⊢ σ) → Comp σ t
eval {Γ} {σ} t = transport (Comp σ) (subst-idSub {t = t}) (⟦ t ⟧ Γ idSub (⇑ˢ Γ Γ idSub idSub-is-neutral))

normalize : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
normalize {Γ} {σ} t = ⇓ Γ σ (eval t)

-- test terms
test-term : [] ⊢ Ans
test-term = (ƛ (` ze)) · (π₁ (π₂ (yes , ((ƛ (` ze)) · no)) , ⟨⟩))

test-term2 : 𝟙 ∷ [] ⊢ 𝟙 ẋ 𝟙
test-term2 = (` ze) , ⟨⟩   

test-term3 : 𝟙 ∷ [] ⊢ Ans ⇒ 𝟙  
test-term3 = (ƛ ((ƛ (` su ze)) · no)) · ((ƛ (ƛ (` su ze))) · (` ze)) -- (λx. (λy. x) no) ((λzw. z) u) 