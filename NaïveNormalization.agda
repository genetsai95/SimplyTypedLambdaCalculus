module NaïveNormalization where

open import STLC
open import STLC.Conversion

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
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → (t ⟶⋆ t') × Normal Γ Ans t')
Comp {Γ} 𝟙 t = Σ (Γ ⊢ 𝟙) (λ t' → (t ⟶⋆ t') × Normal Γ 𝟙 t')
Comp {Γ} (σ ẋ τ) t = Σ (Γ ⊢ σ) (λ t' → Σ (Γ ⊢ τ) (λ t'' → (t ⟶⋆ (t' , t'')) × Comp σ t' × Comp τ t''))
Comp {Γ} (σ ⇒ τ) t = Σ (Γ ⊢ σ ⇒ τ) (λ t' → (t ⟶⋆ t') × ((Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Σ (Θ ⊢ σ) (λ a' → (a ⟶⋆ a') × (Comp τ (rename ρ t' · a')))))

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

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(cs : ⟦ Γ ⟧ˢ ts) → Σ (Δ ⊢ σ) (λ t' → ((t [ ts ]) ⟶⋆ t') × Comp σ t')
⟦ ` x ⟧ Δ ts cs = lookup x ts , ✦ , lookupˢ x cs
⟦ yes ⟧ Δ ts cs = yes , ✦ , yes , ✦ , yes
⟦ no ⟧ Δ ts cs = no , ✦ , no , ✦ , no
⟦ ⟨⟩ ⟧ Δ ts cs = ⟨⟩ , ✦ , ⟨⟩ , ✦ , ⟨⟩
⟦ t , s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = (t' , s') , map-pair t[ts]→t' s[ts]→s' , t' , s' , map-pair ✦ ✦ , t'cs , s'cs
⟦ π₁ t ⟧ Δ ts cs = let (t' , t[ts]→t' , t'' , _ , t'→t'',s , t''cs , _ ) = ⟦ t ⟧ Δ ts cs 
                  in t'' , map-π₁ (t[ts]→t' ▷ t'→t'',s) ▷ (β-π₁ ‣ ✦) , t''cs
⟦ π₂ t ⟧ Δ ts cs = let (t' , t[ts]→t' , _ , t'' , t'→s,t'' , _ , t''cs) = ⟦ t ⟧ Δ ts cs 
                  in t'' , map-π₂ (t[ts]→t' ▷ t'→s,t'') ▷ (β-π₂ ‣ ✦) , t''cs
⟦ _·_ {τ = τ} t s ⟧ Δ ts cs with ⟦ t ⟧ Δ ts cs | ⟦ s ⟧ Δ ts cs
... | t' , t[ts]→t' , t'' , t'→t'' , f | s' , s[ts]→s' , s'cs = let (s'' , s'→s'' , c) = f Δ idRen s' s'cs 
                                                                in (t'' · s'') , 
                                                                   map-app (t[ts]→t' ▷ t'→t'') (s[ts]→s' ▷ s'→s'') ,
                                                                   transport (λ y → Comp τ (y · s'')) (rename-idRen t'') c
⟦ ƛ_ {τ = Ans} t ⟧   Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (ƛ subst t (ts ↑)) , ✦ , 
                                λ Θ ρ s scs → s , ✦ ,
                                              let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                              in t'' , β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
⟦ ƛ_ {τ = 𝟙} t ⟧     Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (ƛ subst t (ts ↑)) , ✦ , 
                                λ Θ ρ s scs → s , ✦ , 
                                              let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , nt'') = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs)
                                              in t'' , β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t'' , nt''
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (ƛ subst t (ts ↑)) , ✦ , 
                                λ Θ ρ s scs → s , ✦ ,
                                              let (t' , t[s∷mr-ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs)
                                              in t₁ , t₂ ,
                                                 β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ t[s∷mr-ts]→t' ▷ t'→t₁,t₂ ,
                                                 t₁cs , t₂cs
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ Δ ts cs = ((ƛ t) [ ts ]) , ✦ , (ƛ subst t (ts ↑)) , ✦ , 
                                λ Θ ρ s scs → s , ✦ ,
                                              let (t' , t[s∷mr-ts]→t' , t'' , t'→t'' , f) = ⟦ t ⟧ Θ (s ∷ mapSub (rename ρ) ts) (scs ∷ renameˢ ρ cs) 
                                              in t'' , (β-ƛ ‣ same (subst-rename-lift-subst ρ ts t s) ‣ ✦) ▷ t[s∷mr-ts]→t' ▷ t'→t'' ,
                                                 λ Θ' ρ' s' c → f Θ' ρ' s' c


⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
⇑ : (Γ : Cxt)(σ : Type) → ((t , _) : Σ (Γ ⊢ σ) (Neutral Γ σ)) → Comp σ t

⇓ Γ Ans c = c
⇓ Γ 𝟙 c = c
⇓ Γ (σ ẋ τ) (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs) with ⇓ Γ σ {t₁} t₁cs | ⇓ Γ τ {t₂} t₂cs
... | t₁' , t₁→t₁' , nt₁' | t₂' , t₂→t₂' , nt₂' = (t₁' , t₂') , t→t₁,t₂ ▷ map-pair t₁→t₁' t₂→t₂' , (nt₁' , nt₂')
⇓ Γ (σ ⇒ τ) (n , t→n , f) = let (z , `ze→z , c) = f (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))) 
                            in let (t' , wk-n·z→t' , nt') = ⇓ (σ ∷ Γ) τ c 
                               in (ƛ t') , t→n ▷ (η-ƛ ‣ (map-ƛ (map-app ✦ `ze→z ▷ wk-n·z→t'))) , (ƛ nt')

⇑ Γ Ans (n , ne) = n , ✦ , (‘ ne)
⇑ Γ 𝟙 (n , ne) = n , ✦ , (‘‘ ne)
⇑ Γ (σ ẋ τ) (n , ne) = π₁ n , π₂ n , η-pair ‣ ✦ , ⇑ Γ σ (π₁ n , π₁ ne) , ⇑ Γ τ (π₂ n , π₂ ne)
⇑ Γ (σ ⇒ τ) (n , ne) = n , ✦ , λ Θ ρ s c → let (s' , s→s' , ns') = ⇓ Θ σ {s} c 
                                              in s' , s→s' , ⇑ Θ τ ((rename ρ n · s') , (rename-ne ρ ne · ns'))

data NeutralSub : Sub Γ Δ → Set where
    [] : NeutralSub ([] {Γ})
    _∷_ : {t : Δ ⊢ σ}{ts : Sub Γ Δ} → Neutral Δ σ t → NeutralSub ts → NeutralSub (t ∷ ts)

⇑ˢ : (Γ Δ : Cxt)(ts : Sub Γ Δ) → NeutralSub ts → ⟦ Γ ⟧ˢ ts
⇑ˢ [] Δ [] [] = []
⇑ˢ (σ ∷ Γ) Δ (t ∷ ts) (nt ∷ ns) = ⇑ Δ σ (t , nt) ∷ ⇑ˢ Γ Δ ts ns

each-is-neutral : (ts : Sub Γ Δ) → (∀{σ} → (x : Γ ∋ σ) → Neutral Δ σ (lookup x ts)) → NeutralSub ts
each-is-neutral [] ne-each = []
each-is-neutral (t ∷ ts) ne-each = ne-each ze ∷ each-is-neutral ts (λ x → ne-each (su x))

idSub-is-neutral : ∀{Γ} → NeutralSub (idSub {Γ})
idSub-is-neutral {Γ} = each-is-neutral idSub each
    where
        each : ∀{σ} → (x : Γ ∋ σ) → Neutral Γ σ (lookup x idSub)
        each {σ} x = transport (Neutral Γ σ) (≡-sym lookup-idSub) (` x)

eval : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Comp σ t')
eval {Γ} t = let (t' , t[id]→t' , t'cs) = ⟦ t ⟧ Γ idSub (⇑ˢ Γ Γ idSub idSub-is-neutral) 
             in t' , transport (λ y → y ⟶⋆ t') (subst-idSub {t = t}) t[id]→t' , t'cs

normalForm : (t : Γ ⊢ σ) → Σ (Γ ⊢ σ) (λ t' → (t ⟶⋆ t') × Normal Γ σ t')
normalForm {Γ} {σ} t = let (t' , t→t' , t'cs) = eval t 
                       in let (t'' , t'→t'' , nt'') = ⇓ Γ σ t'cs 
                          in t'' , t→t' ▷ t'→t'' , nt''

test : [] ⊢ Ans
test = π₁ (((ƛ (` ze)) · yes) , no)

test' : (𝟙 ẋ Ans) ∷ [] ⊢ Ans
test' = π₂ (π₁ (π₂ (⟨⟩ , (` ze)) , no))
