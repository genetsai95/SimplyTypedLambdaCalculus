module NaïveNormalization-without-η where

open import STLC
open import STLC.Reduction
open import STLC.Normal-without-η

Normalizable : Γ ⊢ σ → Set
Normalizable {Γ} {σ} t = Σ (Γ ⊢ σ) (λ n → (t →β* n) × Normal Γ σ n)

normalizable-backward : {t t' : Γ ⊢ σ} → t →β t' → Normalizable t' → Normalizable t
normalizable-backward t→t' (t'' , t'→*t'' , nt'') = t'' , t→t' ‣ t'→*t'' , nt''

normalizable-backward* : {t t' : Γ ⊢ σ} → t →β* t' → Normalizable t' → Normalizable t
normalizable-backward* ✦ c = c
normalizable-backward* (t→u ‣ u→*t') = normalizable-backward t→u ∘ normalizable-backward* u→*t'

thm[naïve-SN] : (t : Γ ⊢ σ) → Normalizable t
thm[naïve-SN] (` x) = (` x) , ✦ , (‘ (` x))
thm[naïve-SN] yes = yes , ✦ , yes
thm[naïve-SN] no = no , ✦ , no
thm[naïve-SN] ⟨⟩ = ⟨⟩ , ✦ , ⟨⟩
thm[naïve-SN] (t , s) with thm[naïve-SN] t | thm[naïve-SN] s
... | t' , t→t' , nt' | s' , s→s' , ns' = (t' , s') , ξ-pair* t→t' s→s' , (nt' , ns')
thm[naïve-SN] (π₁ t) with thm[naïve-SN] t
... | t' , t→t' , (‘ n) = π₁ t' , ξ-π₁* t→t' , (‘ π₁ n)
... | (t' , s') , t→t',s' , (nt' , ns') = t' , ξ-π₁* t→t',s' ▷ (β-π₁ ‣ ✦) , nt'
thm[naïve-SN] (π₂ t) with thm[naïve-SN] t
... | t' , t→t' , (‘ n) = π₂ t' , ξ-π₂* t→t' , (‘ π₂ n)
... | (t' , s') , t→t',s' , (nt' , ns') = s' , ξ-π₂* t→t',s' ▷ (β-π₂ ‣ ✦) , ns'
thm[naïve-SN] (ƛ t) with thm[naïve-SN] t
... | t' , t→t' , nt' = (ƛ t') , ξ-ƛ* t→t' , (ƛ nt')
thm[naïve-SN] (t · s) with thm[naïve-SN] t | thm[naïve-SN] s
... | t' , t→t' , (‘ nt') | s' , s→s' , ns' = (t' · s') , ξ-app* t→t' s→s' , (‘ (nt' · ns'))
... | (ƛ t') , t→ƛt' , (ƛ nt') | s' , s→s' , ns' = {!   !} , {!   !}


Comp : (σ : Type) → Γ ⊢ σ → Set
Comp {Γ} Ans = Normalizable
Comp {Γ} 𝟙 = Normalizable
Comp {Γ} (σ ẋ τ) t = Normalizable t × Comp σ (π₁ t) × Comp τ (π₂ t)
Comp {Γ} (σ ⇒ τ) t = Normalizable t × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ) → Comp σ a → Comp τ (rename ρ t · a))

comp-backward : {t t' : Γ ⊢ σ} → t →β t' → Comp σ t' → Comp σ t
comp-backward {_} {Ans} t→t' (t'' , t'→*t'' , nt'') = t'' , t→t' ‣ t'→*t'' , nt''
comp-backward {_} {𝟙} t→t' (t'' , t'→*t'' , nt'') = t'' , t→t' ‣ t'→*t'' , nt''
comp-backward {_} {σ ẋ τ} t→t' ((t'' , t'→*t'' , nt'') , t₁cs , t₂cs)  = (t'' , t→t' ‣ t'→*t'' , nt'') , comp-backward (ξ-π₁ t→t') t₁cs , comp-backward (ξ-π₂ t→t') t₂cs
comp-backward {Γ} {σ ⇒ τ} {t} t→t' ((t'' , t'→*t'' , nt'') , f) = (t'' , t→t' ‣ t'→*t'' , nt'') , f'
    where
        f' : (Θ : Cxt) (ρ : Ren Γ Θ) (a : Θ ⊢ σ) → Comp σ a → Comp τ (rename ρ t · a)
        f' Θ ρ a c = comp-backward (ξ-app (rename-ξ ρ t→t') (same refl)) (f Θ ρ a c)

comp-backward* : {t t' : Γ ⊢ σ} → t →β* t' → Comp σ t' → Comp σ t
comp-backward* ✦ c = c
comp-backward* (t→u ‣ u→*t') = comp-backward t→u ∘ comp-backward* u→*t'

infix 25 _[_]
_[_] : Γ ⊢ σ → Sub Γ Δ → Δ ⊢ σ
t [ ts ] = subst t ts

data ⟦_⟧ˢ {Δ : Cxt} : (Γ : Cxt) → Sub Γ Δ → Set where
    [] : ⟦ [] ⟧ˢ ([] {Δ})
    _∷_ : {t : Δ ⊢ σ}{ts : Sub Γ Δ} → Comp σ t → ⟦ Γ ⟧ˢ ts → ⟦ (σ ∷ Γ) ⟧ˢ (t ∷ ts)

lookupˢ : {ts : Sub Γ Δ}(x : Γ ∋ σ) → ⟦ Γ ⟧ˢ ts → Comp σ (lookup x ts)
lookupˢ ze (c ∷ _) = c
lookupˢ (su x) (_ ∷ cs) = lookupˢ x cs

⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Normalizable t
⇓ Γ Ans u = u
⇓ Γ 𝟙 u = u
⇓ Γ (_ ẋ _) u = pr₁ u
⇓ Γ (_ ⇒ _) u = pr₁ u

⇑ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ} → Neutral Γ σ t → Comp σ t
⇑ Γ Ans {t} nt = t , ✦ , (‘ nt)
⇑ Γ 𝟙 {t} nt = t , ✦ , (‘ nt)
⇑ Γ (σ ẋ τ) {t} nt = (t , ✦ , (‘ nt)) , ⇑ Γ σ (π₁ nt) , ⇑ Γ τ (π₂ nt)
⇑ Γ (σ ⇒ Ans) {t} nt = (t , ✦ , (‘ nt)) , f
    where
        f : (Θ : Cxt) (ρ : Ren Γ Θ) (a : Θ ⊢ σ) → Comp σ a → Comp Ans (rename ρ t · a)
        f Θ ρ a c = let (a' , a→a' , na') = ⇓ Θ σ c 
                    in (rename ρ t · a') , ξ-app* ✦ a→a' , (‘ (rename-ne ρ nt · na'))
⇑ Γ (σ ⇒ 𝟙) {t} nt = (t , ✦ , (‘ nt)) , f
    where
        f : (Θ : Cxt) (ρ : Ren Γ Θ) (a : Θ ⊢ σ) → Comp σ a → Comp 𝟙 (rename ρ t · a)
        f Θ ρ a c = let (a' , a→a' , na') = ⇓ Θ σ c 
                    in (rename ρ t · a') , ξ-app* ✦ a→a' , (‘ (rename-ne ρ nt · na'))
⇑ Γ (σ ⇒ (τ ẋ τ')) {t} nt = (t , ✦ , (‘ nt)) , {!   !}
    where
        f : (Θ : Cxt) (ρ : Ren Γ Θ) (a : Θ ⊢ σ) → Comp σ a → Comp (τ ẋ τ') (rename ρ t · a)
        f Θ ρ a c = let (a' , a→a' , na') = ⇓ Θ σ c 
                    in ((rename ρ t · a') , ξ-app* ✦ a→a' , (‘ (rename-ne ρ nt · na'))) , {! ⇑ Θ τ  !} , {!   !}
⇑ Γ (σ ⇒ (τ ⇒ τ')) {t} nt = (t , ✦ , (‘ nt)) , {!   !}



⟦_⟧ : (t : Γ ⊢ σ)(Δ : Cxt)(ts : Sub Γ Δ) → ⟦ Γ ⟧ˢ ts → Comp σ (t [ ts ])
⟦ ` x ⟧ Δ ts cs = lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , ✦ , yes
⟦ no ⟧ Δ ts cs = no , ✦ , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩
⟦ _,_ {_} {σ} {τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
...                             | tcs | scs with ⇓ Δ σ tcs | ⇓ Δ τ scs
...                             | t' , t[ts]→t' , nt' | s' , s[ts]→s' , ns' = ((t' , s') , ξ-pair* t[ts]→t' s[ts]→s' , (nt' , ns')) ,
                                                                                comp-backward {t' = t [ ts ]} β-π₁ tcs ,
                                                                                comp-backward {t' = s [ ts ]} β-π₂ scs
⟦ π₁ t ⟧ Δ ts cs = pr₁ (pr₂ (⟦ t ⟧ Δ ts cs))
⟦ π₂ t ⟧ Δ ts cs = pr₂ (pr₂ (⟦ t ⟧ Δ ts cs))
⟦ _·_ {_} {σ} {τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | (t'' , t'→*t'' , nt'') , f | scs = transport (λ - → Comp τ (- · subst s ts)) (rename-idRen (t [ ts ])) (f Δ idRen (s [ ts ]) scs)
⟦ ƛ_ {σ} {_} {Ans} t ⟧ Δ ts cs = {! ⟦ t ⟧ (σ ∷ Δ) (ts ↑) !}
⟦ ƛ_ {τ = 𝟙} t ⟧ Δ ts cs = {!   !}
⟦ ƛ_ {τ = τ ẋ τ₁} t ⟧ Δ ts cs = {!   !}
⟦ ƛ_ {τ = τ ⇒ τ₁} t ⟧ Δ ts cs = {!   !}

-- ⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t
-- ⇑ Γ Ans (n , ne) = n , ✦ , (‘ ne)
-- ⇑ Γ 𝟙 (n , ne) = n , ✦ , (‘ ne)
-- ⇑ Γ (σ ẋ τ) (n , ne) = inl (n , ✦ , ne)
-- ⇑ Γ (σ ⇒ τ) (n , ne) = n , ✦ , inl ne


-- mapˢ : (fₜ : ∀{σ} → Δ ⊢ σ → Θ ⊢ σ)(fₛ : ∀{σ} → {t : Δ ⊢ σ} → Comp σ t → Comp σ (fₜ t)) → {ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub fₜ ts)
-- mapˢ fₜ fₛ [] = []
-- mapˢ fₜ fₛ (c ∷ cs) = fₛ c ∷ mapˢ fₜ fₛ cs

-- Comp : (σ : Type) → Γ ⊢ σ → Set
-- Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t →β* t') × Normal Γ Ans t')
-- Comp {Γ} 𝟙 t = Σ (Γ ⊢ 𝟙) (λ t' → (t →β* t') × Normal Γ 𝟙 t')
-- Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ ẋ τ) (λ t' → (t →β* t') × Neutral Γ (σ ẋ τ) t') ⊎ Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (t →β* (t' , t'')) × Comp σ t' × Comp τ t''))
-- Comp {Γ} (σ ⇒ τ) t = 
--    -- Σ (σ ∷ Γ ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Comp τ (rename (lift ρ) t' [ a /x])))
--    -- Σ (σ ∷ Γ ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Σ (Θ ⊢ σ) (λ a' → (a →β* a') × Comp τ (rename (lift ρ) t' [ a' /x]))))
--    Σ (Γ ⊢ σ ⇒ τ) (λ t' → (t →β* t') × (Neutral Γ (σ ⇒ τ) t' ⊎ ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) →  Σ (Θ ⊢ σ) (λ a' → (a →β* a') × Comp τ (rename ρ t' · a')))))

-- rename-comp : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
-- rename-comp {σ = Ans} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
-- rename-comp {σ = 𝟙} ρ t (t' , t→t' , nt') = rename ρ t' , map-rename ρ t→t' , rename-nf ρ nt'
-- rename-comp {σ = σ ẋ τ} ρ t (inl (t' , t→t' , nt')) = inl (rename ρ t' , map-rename ρ t→t' , rename-ne ρ nt')
-- rename-comp {σ = σ ẋ τ} ρ t (inr (s , s' , t→s,s' , scs , s'cs)) = inr (rename ρ s , rename ρ s' , map-rename ρ t→s,s' ▷ map-pair ✦ ✦ , rename-comp ρ s scs , rename-comp ρ s' s'cs)
-- rename-comp {σ = σ ⇒ τ} ρ t (t' , t→t' , inl nt') = rename ρ t' , map-rename ρ t→t' , inl (rename-ne ρ nt')
-- rename-comp {σ = σ ⇒ τ} ρ t (t' , t→t' , inr f) = rename ρ t' , map-rename ρ t→t' , inr λ Θ ρ' s c → let (s' , s→s' , c') = f Θ (concatRen ρ ρ') s c 
--                                                                                                      in s' , s→s' , transport (λ y → Comp τ (y · s')) (rename-concatRen≡rename-rename ρ ρ' t') c'

-- renameˢ : (ρ : Ren Δ Θ){ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (mapSub (rename ρ) ts)
-- renameˢ ρ = mapˢ (rename ρ) (λ {σ} {t} → rename-comp ρ t)

-- ⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')
-- ⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

-- ⇓ Γ Ans cs = cs
-- ⇓ Γ 𝟙 cs = cs
-- ⇓ Γ (σ ẋ τ) (inl (t' , t→t' , ne)) = t' , t→t' , (‘ ne)
-- ⇓ Γ (σ ẋ τ) (inr (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs)) with ⇓ Γ σ t₁cs | ⇓ Γ τ t₂cs
-- ... | t₁' , t₁→t₁' , nf₁ | t₂' , t₂→t₂' , nf₂ = (t₁' , t₂') , t→t₁,t₂ ▷ map-pair t₁→t₁' t₂→t₂' , (nf₁ , nf₂)
-- ⇓ Γ (σ ⇒ τ) (t' , t→t' , inl ne) = t' , t→t' , (‘ ne)
-- ⇓ Γ (σ ⇒ τ) (t' , t→t' , inr f) = let (z , `ze→z , zcs) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
--                                   in let (t'' , ren-t'·z→t'' , nt'') = ⇓ (σ ∷ Γ) τ zcs 
--                                      in (ƛ t'') , t→t' ▷ (same {!   !} ‣ {!   !}) , (ƛ nt'')

-- ⇑ Γ Ans (n , ne) = n , ✦ , (‘ ne)
-- ⇑ Γ 𝟙 (n , ne) = n , ✦ , (‘ ne)
-- ⇑ Γ (σ ẋ τ) (n , ne) = inl (n , ✦ , ne)
-- ⇑ Γ (σ ⇒ τ) (n , ne) = n , ✦ , inl ne

----------------------------------

-- ⇓ Γ Ans cs = cs
-- ⇓ Γ 𝟙 cs = cs
-- ⇓ Γ (σ ẋ τ) (inl (t' , t→t' , nt')) = t' , t→t' , (‘ nt')
-- ⇓ Γ (σ ẋ τ) (inr (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs)) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
-- ... | n₁ , t₁→n₁ , nf₁ | n₂ , t₂→n₂ , nf₂ = (n₁ , n₂) , t→t₁,t₂ ▷ map-pair t₁→n₁ t₂→n₂ , (nf₁ , nf₂)
-- ⇓ Γ (σ ⇒ τ) (inl (t' , t→t' , nt')) = t' , t→t' , (‘ nt')
-- ⇓ Γ (σ ⇒ τ) (inr (t' , t→t' , f)) = let (z , `ze→z , zcs) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
--                                      in let (t'' , ren-t'·z→t'' , nt'') = ⇓ (σ ∷ Γ) τ zcs 
--                                         in (ƛ t'') , t→t' ▷ {!   !} , (ƛ nt'')
--                                           --   where
--                                           --    eq : t' ≡ rename (lift wk) t' [ ` ze /x]
--                                           --    eq = ≡-sym ((rename (lift wk) t' [ ` ze /x])
--                                           --             ≡⟨ cong (λ y → rename (lift wk) y [ ` ze /x]) (≡-sym (subst-idSub {t = t'})) ⟩ 
--                                           --                (rename (lift wk) (subst t' (idSub ↑)) [ ` ze /x])
--                                           --             ≡⟨ subst-rename-lift-subst wk idSub t' (` ze) ⟩ 
--                                           --                 subst t' (idSub ↑)
--                                           --             ≡⟨ subst-idSub {t = t'} ⟩ 
--                                           --                 t'
--                                           --             ∎)


-- ⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t →β* t') × Normal Γ σ t')
-- ⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

-- ⇓ Γ Ans cs = cs
-- ⇓ Γ 𝟙 cs = cs
-- ⇓ Γ (σ ẋ τ) (inl (t' , t→t' , nt')) = t' , t→t' , (‘ nt')
-- ⇓ Γ (σ ẋ τ) (inr (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs)) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
-- ... | n₁ , t₁→n₁ , nf₁ | n₂ , t₂→n₂ , nf₂ = (n₁ , n₂) , t→t₁,t₂ ▷ map-pair t₁→n₁ t₂→n₂ , (nf₁ , nf₂)
-- ⇓ Γ (σ ⇒ τ) (inl (t' , t→t' , nt')) = t' , t→t' , (‘ nt')
-- ⇓ Γ (σ ⇒ τ) (inr (t' , t→ƛt' , f)) = let (z , `ze→z , zcs) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
--                                      in let (t'' , ren-t'[z]→t'' , nt'') = ⇓ (σ ∷ Γ) τ zcs 
--                                         in (ƛ t'') , 
--                                             t→ƛt' ▷ map-ƛ (same eq ‣ map-/x (rename (lift wk) t') `ze→z ▷ ren-t'[z]→t'') ,
--                                            (ƛ nt'')
--                                             where
--                                              eq : t' ≡ rename (lift wk) t' [ ` ze /x]
--                                              eq = ≡-sym ((rename (lift wk) t' [ ` ze /x])
--                                                       ≡⟨ cong (λ y → rename (lift wk) y [ ` ze /x]) (≡-sym (subst-idSub {t = t'})) ⟩ 
--                                                          (rename (lift wk) (subst t' (idSub ↑)) [ ` ze /x])
--                                                       ≡⟨ subst-rename-lift-subst wk idSub t' (` ze) ⟩ 
--                                                           subst t' (idSub ↑)
--                                                       ≡⟨ subst-idSub {t = t'} ⟩ 
--                                                           t'
--                                                       ∎)


-- ⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) →β* t') × Comp σ t')
-- ⟦ ` x ⟧ Δ ts cs = lookup x ts , ✦ , lookupˢ x cs
-- ⟦ yes ⟧ Δ ts cs = yes , ✦ , yes , ✦ , yes
-- ⟦ no ⟧ Δ ts cs = no , ✦ , no , ✦ , no
-- ⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩ , ✦ , ⟨⟩
-- ⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
-- ... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , map-pair t[ts]→t' s[ts]→s' , inr (t' , s' , ✦ , t'cs , s'cs)
-- ⟦ π₁ t ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs
-- ... | t' , t[ts]→t' , inl (t'' , t'→t'' , (‘ x)) = π₁ t'' , map-π₁ (t[ts]→t' ▷ t'→t'') , compNormal (‘ π₁ x)
-- ... | t' , t[ts]→t' , inl ((t₁ , _)  , t'→t₁,t₂ , (nt₁ , _)) = t₁ , map-π₁ (t[ts]→t' ▷ t'→t₁,t₂) ▷ (β-π₁ ‣ ✦) , compNormal nt₁
-- ... | t' , t[ts]→t' , inr (t'' , _ , t'→t'',s , t''cs , _) = t'' , map-π₁ (t[ts]→t' ▷ t'→t'',s) ▷ (β-π₁ ‣ ✦) , t''cs
-- ⟦ π₂ t ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs
-- ... | t' , t[ts]→t' , inl (t'' , t'→t'' , (‘ x)) = π₂ t'' , map-π₂ (t[ts]→t' ▷ t'→t'') , compNormal (‘ π₂ x)
-- ... | t' , t[ts]→t' , inl ((_ , t₂) , t'→t₁,t₂ , (_ , nt₂)) = t₂ , map-π₂ (t[ts]→t' ▷ t'→t₁,t₂) ▷ (β-π₂ ‣ ✦) , compNormal nt₂
-- ... | t' , t[ts]→t' , inr (_ , t'' , t'→s,t'' , _ , t''cs) = t'' , map-π₂ (t[ts]→t' ▷ t'→s,t'') ▷ (β-π₂ ‣ ✦) , t''cs
-- ⟦ _·_ {σ = σ} {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
-- ... | t' , t[ts]→t' , inl (t'' , t'→t'' , (‘ x)) | s' , s[ts]→s' , s'cs = let (s'' , s'→s'' , ns'') = ⇓ Δ σ s'cs
--                                                                           in (t'' · s'') , map-app (t[ts]→t' ▷ t'→t'') (s[ts]→s' ▷ s'→s'') , compNormal (‘ (x · ns''))
-- ... | t' , t[ts]→t' , inl ((ƛ t'') , t'→ƛt'' , (ƛ nt'')) | s' , s[ts]→s' , s'cs = {!   !}
-- ... | t' , t[ts]→t' , inr x | s' , s[ts]→s' , s'cs = {!   !}
-- ⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = {!   !}
-- ⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = {!   !}
-- ⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = {!   !}
-- ⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = {!   !}
-- -- ⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
-- -- ... | t' , t[ts]→t' , t'' , t'→ƛt'' , f | s' , s[ts]→s' , s'cs = let (s'' , s'→s'' , s''cs) = f Δ idRen s' s'cs 
-- --                                                                  in (t'' [ s'' /x]) , map-app (t[ts]→t' ▷ t'→ƛt'') (s[ts]→s' ▷ s'→s'') ▷ (β-ƛ ‣ ✦) ,
-- --                                                                     transport (λ y → Comp τ (y [ s'' /x])) (rename-idRen t'') s''cs
-- -- ⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
-- --                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
-- --                                             in s , ✦ ,  t'' , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
-- -- ⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
-- --                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
-- --                                             in s , ✦ , t'' , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
-- -- ⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ ,
-- --                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
-- --                                             in s , ✦ , t₁ , t₂ , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t₁,t₂ , t₁cs , t₂cs
-- -- ⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (t [ (ts ↑) ]) , ✦ , 
-- --                                 λ Θ ρ s c → let (t' , t[s∷mr-ts]→t' , t'' , t'→ƛt'' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (c ∷ renameˢ ρ cs)
-- --                                             in s , ✦ , t'' , same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→ƛt'' , λ Θ' ρ' s' c' → f Θ' ρ' s' c'


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