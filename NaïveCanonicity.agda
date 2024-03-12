module NaïveCanonicity where

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
Comp Ans t = Σ ([] ⊢ Ans) (λ t' → (t →β* t') × ((t' ≡ yes) ⊎ (t' ≡ no)))
Comp 𝟙 t = ⊤
Comp (σ ⇒ τ) t = Σ ([] ⊢ σ ⇒ τ) (λ t' → (t →β* t') × ((a : [] ⊢ σ)(u : Comp σ a) → Comp τ (t' · a)))
Comp (σ ẋ τ) t = Σ ([] ⊢ σ) (λ t' → Σ ([] ⊢ τ) (λ t'' → ((π₁ t →β* t') × (π₂ t →β* t'') × Comp σ t' × Comp τ t'')))


-- context -> corresponding computability structures for closed terms
data ⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ → Set where
    [] : ⟦ [] ⟧ˢ []
    _∷_ : ∀{σ} → {t : [] ⊢ σ}{ts : ⟦ Γ ⟧ᶜ} → Comp σ t → ⟦ Γ ⟧ˢ ts → ⟦ (σ ∷ Γ) ⟧ˢ (t ∷ ts)

lookupˢ : {ts : ⟦ Γ ⟧ᶜ}(x : Γ ∋ σ) → ⟦ Γ ⟧ˢ ts → Comp σ (lookup x ts)
lookupˢ ze (c ∷ _) = c
lookupˢ (su x) (_ ∷ cs) = lookupˢ x cs



-- computability morphism
⟦_⟧ : (t : Γ ⊢ σ) → (ts : ⟦ Γ ⟧ᶜ)(cs : ⟦ Γ ⟧ˢ ts) → Σ ([] ⊢ σ) (λ t' → ((t [ ts ]) →β* t') × Comp σ t')
⟦ ` x ⟧ ts cs = ((` x) [ ts ]) , ✦ , lookupˢ x cs
⟦ yes ⟧ ts cs = yes , ✦ , yes , ✦ , inl refl
⟦ no ⟧ ts cs = no , ✦ , no , ✦ , inr refl
⟦ ⟨⟩ ⟧ ts cs = ⟨⟩ , ✦ , `nil
⟦ t , s ⟧ ts cs with ⟦ t ⟧ ts cs | ⟦ s ⟧ ts cs
... | t' , t[ts]→t' , tcs | s' , s[ts]→s' , scs = (t' , s') , ξ-pair* t[ts]→t' s[ts]→s' , t' , s' , β-π₁ ‣ ✦ , β-π₂ ‣ ✦ , tcs , scs
⟦ π₁ t ⟧ ts cs with ⟦ t ⟧ ts cs
... | t' , t[ts]→t' , t'' , _ , π₁t'→t'' , _ , t''cs , _ = t'' , ξ-π₁* t[ts]→t' ▷ π₁t'→t'' , t''cs
⟦ π₂ t ⟧ ts cs with ⟦ t ⟧ ts cs
... | t' , t[ts]→t' , _ , t'' , _ , π₂t'→t'' , _ , t''cs = t'' , ξ-π₂* t[ts]→t' ▷ π₂t'→t'' , t''cs
⟦ t · s ⟧ ts cs with ⟦ t ⟧ ts cs | ⟦ s ⟧ ts cs
... | t' , t[ts]→t' , t'' , t'→t'' , f | s' , s[ts]→s' , scs = (t'' · s') , ξ-app* (t[ts]→t' ▷ t'→t'') s[ts]→s' , f s' scs
⟦ ƛ_ {τ = Ans} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , (ƛ subst t (ts ↑)) , ✦ , 
                          λ t' c → let (t'' , t[t'∷ts]→t'' , t''' , t''→t''' , eq) = ⟦ t ⟧ (t' ∷ ts) (c ∷ cs) 
                                   in t''' , (β-ƛ ‣ same (lem[sub1] t ts t') ‣ ✦) ▷ t[t'∷ts]→t'' ▷ t''→t''' , eq
⟦ ƛ_ {τ = 𝟙} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , ((ƛ t) [ ts ]) , ✦ , λ t' c → `nil
⟦ ƛ_ {τ = τ ẋ τ'} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , (ƛ subst t (ts ↑)) , ✦ , 
                              λ t' c → let (t'' , t[t'∷ts]→t'' , s , s' , π₁t''→s , π₂t''→s' , scs , s'cs) = ⟦ t ⟧ (t' ∷ ts) (c ∷ cs)
                                       in s , s' ,
                                          ξ-π₁* ((β-ƛ ‣ same (lem[sub1] t ts t') ‣ ✦) ▷ t[t'∷ts]→t'') ▷ π₁t''→s ,
                                          ξ-π₂* ((β-ƛ ‣ same (lem[sub1] t ts t') ‣ ✦) ▷ t[t'∷ts]→t'') ▷ π₂t''→s' , scs , s'cs
⟦ ƛ_ {τ = τ ⇒ τ'} t ⟧ ts cs = ((ƛ t) [ ts ]) , ✦ , (ƛ subst t (ts ↑)) , ✦ , 
                              λ t' c → let (t'' , t[t'∷ts]→t'' , t''' , t''→t''' , f) = ⟦ t ⟧ (t' ∷ ts) (c ∷ cs)
                                       in t''' , (β-ƛ ‣ same (lem[sub1] t ts t') ‣ ✦) ▷ t[t'∷ts]→t'' ▷ t''→t''' , λ s c' → f s c' 

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
... | t' , t[[]]→t' , .yes , t'→yes , inl refl = inl (β-red (same (≡-sym ([[]] t)) ‣ t[[]]→t' ▷ t'→yes))
... | t' , t[[]]→t' , .no , t'→no , inr refl = inr (β-red (same (≡-sym ([[]] t)) ‣ t[[]]→t' ▷ t'→no))

test-term : [] ⊢ Ans
test-term = π₁ (yes , no)
    -- (ƛ (` ze)) · (π₁ (π₂ (yes , ((ƛ (` ze)) · no)) , ⟨⟩))

test-canonicity : ([] ⊢ test-term ≐ yes ∶ Ans) ⊎ ([] ⊢ test-term ≐ no ∶ Ans)
test-canonicity = thm[canonicity] test-term