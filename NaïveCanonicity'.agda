module NaïveCanonicity' where

open import Prelude
open import STLC
open import STLC.Reduction

-- context -> list of closed terms with corresponding types
⟦_⟧ᶜ : Cxt → Set
⟦ Γ ⟧ᶜ = Sub Γ []


-- closed term substitution
_[_] :  Γ ⊢ σ → ⟦ Γ ⟧ᶜ → [] ⊢ σ
t [ ts ] = subst t ts

-- computability structure

Comp : (σ : Type) → [] ⊢ σ → Set
Comp Ans t = 
    (t →β* yes) ⊎ (t →β* no)
    -- Σ ([] ⊢ Ans) (λ t' → (t →β* t') × (((t' ≡ yes) ⊎ (t' ≡ no))))
Comp 𝟙 t = ⊤
Comp (σ ⇒ τ) t = Σ (σ ∷ [] ⊢ τ) (λ t' → (t →β* (ƛ t')) × ((a : [] ⊢ σ)(u : Comp σ a) → Comp τ (t' [ a /x])))
Comp (σ ẋ τ) t = 
    -- Comp σ (π₁ t) × Comp τ (π₂ t) 
    -- Σ ([] ⊢ σ) (λ t' → Σ ([] ⊢ τ) (λ t'' → ((π₁ t →β* t') × (π₂ t →β* t'') × Comp σ t' × Comp τ t'')))
    Σ ([] ⊢ σ) (λ t' → Σ ([] ⊢ τ) (λ t'' → ((t →β* (t' , t'')) × Comp σ t' × Comp τ t'')))

-- context -> corresponding computability structures for closed terms
data ⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ → Set where
    [] : ⟦ [] ⟧ˢ []
    _∷_ : ∀{σ} → {t : [] ⊢ σ}{ts : ⟦ Γ ⟧ᶜ} → Comp σ t → ⟦ Γ ⟧ˢ ts → ⟦ (σ ∷ Γ) ⟧ˢ (t ∷ ts)

lookupˢ : {ts : ⟦ Γ ⟧ᶜ}(x : Γ ∋ σ) → ⟦ Γ ⟧ˢ ts → Comp σ (lookup x ts)
lookupˢ ze (c ∷ _) = c
lookupˢ (su x) (_ ∷ cs) = lookupˢ x cs



-- computability morphism
-- -- output without reduction
-- ⟦_⟧ : (t : Γ ⊢ σ) → (ts : ⟦ Γ ⟧ᶜ)(cs : ⟦ Γ ⟧ˢ ts) → Comp σ (t [ ts ])
-- ⟦ ` x ⟧ ts cs = lookupˢ x cs
-- ⟦ yes ⟧ ts cs = inl ✦
-- ⟦ no ⟧ ts cs = inr ✦
-- ⟦ ⟨⟩ ⟧ ts cs = `nil
-- ⟦ t , s ⟧ ts cs = (t [ ts ]) , (s [ ts ]) , ξ-pair* ✦ ✦ , ⟦ t ⟧ ts cs , ⟦ s ⟧ ts cs
-- ⟦ π₁ t ⟧ ts cs = let (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ ts cs
--                  in {!   !}
-- ⟦ π₂ t ⟧ ts cs = let (t₁ , t₂ , t→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ ts cs 
--                  in {!   !}
-- ⟦ t · s ⟧ ts cs with ⟦ t ⟧ ts cs | ⟦ s ⟧ ts cs
-- ... | t' , t[ts]→ƛt' , f | scs = {!   !}
-- ⟦ ƛ t ⟧ ts cs = {!   !}

⟦_⟧ : (t : Γ ⊢ σ) → (ts : ⟦ Γ ⟧ᶜ)(cs : ⟦ Γ ⟧ˢ ts) → Σ ([] ⊢ σ) (λ t' → ((t [ ts ]) →β* t') × Comp σ t')
⟦ yes ⟧ ts cs = yes , ✦ , inl ✦
⟦ ` x ⟧ ts cs = ((` x) [ ts ]) , ✦ , lookupˢ x cs
⟦ no ⟧ ts cs = no , ✦ , inr ✦
⟦ ⟨⟩ ⟧ ts cs = ⟨⟩ , ✦ , `nil
⟦ t , s ⟧ ts cs with ⟦ t ⟧ ts cs | ⟦ s ⟧ ts cs --(t [ ts ]) , (s [ ts ]) , ξ-pair* ✦ ✦ , ⟦ t ⟧ ts cs , ⟦ s ⟧ ts cs
... | t' , t[ts]→t' , t'cs | s' , s[ts]→s' , s'cs = ((t [ ts ]) , (s [ ts ])) , ξ-pair* ✦ ✦ , t' , s' , ξ-pair* t[ts]→t' s[ts]→s' , t'cs , s'cs
⟦ π₁ t ⟧ ts cs = let (t' , t[ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ ts cs
                 in t₁ , ξ-π₁* (t[ts]→t' ▷ t'→t₁,t₂) ▷ (β-π₁ ‣ ✦) , t₁cs
⟦ π₂ t ⟧ ts cs = let (t' , t[ts]→t' , t₁ , t₂ , t'→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ ts cs
                 in t₂ , ξ-π₂* (t[ts]→t' ▷ t'→t₁,t₂) ▷ (β-π₂ ‣ ✦) , t₂cs
⟦ t · s ⟧ ts cs with ⟦ t ⟧ ts cs | ⟦ s ⟧ ts cs
... | t' , t[ts]→t' , t'' , t'→ƛt'' , f | s' , s[ts]→s' , s'cs = (t'' [ s' /x]) , ξ-app* (t[ts]→t' ▷ t'→ƛt'') s[ts]→s' ▷ (β-ƛ ‣ ✦) , f s' s'cs
⟦ ƛ_ {τ = Ans} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , subst t (ts ↑) , ✦ , 
                            λ t' c → let (t'' , t[t'∷ts]→t'' , t''cs) = ⟦ t ⟧ (t' ∷ ts) (c ∷ cs) 
                                     in {! t''cs  !}
⟦ ƛ_ {τ = 𝟙} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , subst t (ts ↑) , ✦ , λ t' c → `nil
⟦ ƛ_ {τ = σ ẋ τ} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , subst t (ts ↑) , ✦ , 
                              λ t' c → let (t'' , t[t'∷ts]→t'' , t₁ , t₂ , t''→t₁,t₂ , t₁cs , t₂cs) = ⟦ t ⟧ (t' ∷ ts) (c ∷ cs) 
                                       in t₁ , t₂ , (same (lem[sub1] t ts t') ‣ t[t'∷ts]→t'') ▷ t''→t₁,t₂ , t₁cs , t₂cs
⟦ ƛ_ {τ = σ ⇒ τ} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , subst t (ts ↑) , ✦ , 
                              λ t' c → let (t'' , t[t'∷ts]→t'' , t''' , t''→ƛt''' , f) = ⟦ t ⟧ (t' ∷ ts) (c ∷ cs) 
                                       in t''' , same (lem[sub1] t ts t') ‣ (t[t'∷ts]→t'' ▷ t''→ƛt''') , λ s c → f s c

-- canonicity   
[[]] : (t : [] ⊢ σ) → (t [ [] ]) ≡ t
[[]] yes = refl
[[]] no = refl
[[]] ⟨⟩ = refl
[[]] (t , s) = pair-term-≡ ([[]] t) ([[]] s)
[[]] (π₁ t) = cong π₁ ([[]] t)
[[]] (π₂ t) = cong π₂ ([[]] t)
[[]] (ƛ t) = cong ƛ_ subst-idSub
[[]] (t · s) = app-term-≡ ([[]] t) ([[]] s)

thm[canonicity] : (t : [] ⊢ Ans) → ([] ⊢ t ≐ yes ∶ Ans) ⊎ ([] ⊢ t ≐ no ∶ Ans)
thm[canonicity] t with ⟦ t ⟧ [] [] 
... | t' , t[[]]→t' , inl t'→yes = inl (β-red (same (≡-sym ([[]] t)) ‣ (t[[]]→t' ▷ t'→yes)))
... | t' , t[[]]→t' , inr t'→no = inr (β-red (same (≡-sym ([[]] t)) ‣ (t[[]]→t' ▷ t'→no)))

test-term : [] ⊢ Ans
test-term = (ƛ (` ze)) · (π₁ (π₂ (yes , ((ƛ (` ze)) · no)) , ⟨⟩))

test-canonicity : ([] ⊢ test-term ≐ yes ∶ Ans) ⊎ ([] ⊢ test-term ≐ no ∶ Ans)
test-canonicity = thm[canonicity] test-term 