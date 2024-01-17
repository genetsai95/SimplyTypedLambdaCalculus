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
Comp {Γ} Ans t = Σ (Γ ⊢ Ans) (λ t' → Normal Γ Ans t' × (t' ≡ t))
Comp 𝟙 t = ⊤
Comp (σ ẋ τ) t = Comp σ (π₁ t) × Comp τ (π₂ t)
Comp {Γ} (σ ⇒ τ) t = (Θ : Cxt)(ρ : Ren Γ Θ)(a : Θ ⊢ σ)(u : Comp σ a) → Comp τ ((rename ρ t) · a)

comp-β-π₁ : {t : Γ ⊢ σ}{s : Γ ⊢ τ} → Comp σ (π₁ (t , s)) → Comp σ t
comp-β-π₁ u = {!   !}

⟦_⟧ᶜ : Cxt → Cxt → Set
⟦ Γ ⟧ᶜ Δ = Sub Γ Δ

⟦_⟧ˢ : (Γ : Cxt) → ⟦ Γ ⟧ᶜ Δ → Set
⟦ Γ ⟧ˢ ts = ∀{τ} → (x : Γ ∋ τ) → Comp τ (lookup x ts)


ext-s : {ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → {t : Δ ⊢ σ} → Comp σ t → ⟦ σ ∷ Γ ⟧ˢ (t ∷ ts)
ext-s u s ze = s
ext-s u s (su x) = u x

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

comp-under-rename : (ρ : Ren Γ Δ)(t : Γ ⊢ σ) → Comp σ t → Comp σ (rename ρ t)
comp-under-rename {σ = Ans} ρ t (t' , nt' , eq') = rename ρ t' , (rename-nf ρ nt' , cong (rename ρ) eq')
comp-under-rename {σ = 𝟙} _ _ _ = `nil
comp-under-rename {σ = σ ẋ τ} ρ t (c₁ , c₂) = comp-under-rename ρ (π₁ t) c₁ , comp-under-rename ρ (π₂ t) c₂
comp-under-rename {σ = σ ⇒ τ} ρ t c Θ ρ' a u = {!  c ? ? a u  !} --comp-under-rename ρ t c Θ ρ' a u

rename-c : Ren Δ Θ → ⟦ Γ ⟧ᶜ Δ → ⟦ Γ ⟧ᶜ Θ
rename-c ρ = mapSub (rename ρ)

rename-s : {ρ : Ren Δ Θ}{ts : ⟦ Γ ⟧ᶜ Δ} → ⟦ Γ ⟧ˢ ts → ⟦ Γ ⟧ˢ (rename-c ρ ts)
rename-s u x = {! u x   !}

⟦_⟧ : (t : Γ ⊢ σ) → (Δ : Cxt)(ts : ⟦ Γ ⟧ᶜ Δ)(u : ⟦ Γ ⟧ˢ ts) → Comp σ (subst t ts)
⟦ ` x ⟧ Δ a u = u x
⟦ yes ⟧ Δ a u = yes , (yes , refl)
⟦ no ⟧ Δ a u = no , (no , refl)
⟦ ⟨⟩ ⟧ Δ a u = `nil
⟦ t , s ⟧ Δ a u = {!   !} -- ⟦ t ⟧ Δ a u , ⟦ s ⟧ Δ a u
⟦ π₁ t ⟧ Δ a u = pr₁ (⟦ t ⟧ Δ a u)
⟦ π₂ t ⟧ Δ a u = pr₂ (⟦ t ⟧ Δ a u)
⟦ t · s ⟧ Δ a u = {!   !} -- ⟦ t ⟧ Δ a u Δ (λ x → x) (subst a s) (⟦ s ⟧ Δ a u)
⟦ ƛ t ⟧ Δ a u = λ Θ ρ a' u' → {!   !} -- ⟦ t ⟧ Θ (ext-c (rename-c ρ a) a') (ext-s (rename-s u) u')

⇓ : (Γ : Cxt)(σ : Type){t : Γ ⊢ σ}(u : Comp σ t) → ∃[ t' ∶ Γ ⊢ σ ] Normal Γ σ t'
⇑ : (Γ : Cxt)(σ : Type) → ((n' , _) : ∃[ n ∶ Γ ⊢ σ ] Neutral Γ σ n) → Comp σ n'

⇓ Γ Ans (t , p) = t , pr₁ p
⇓ Γ 𝟙 u = ⟨⟩ , ⟨⟩
⇓ Γ (σ ẋ τ) (u , v) with ⇓ Γ σ u | ⇓ Γ τ v
... | (t , nt) | (s , ns) = (t , s) , (nt , ns)
⇓ Γ (σ ⇒ τ) u with ⇓ (σ ∷ Γ) τ (u (σ ∷ Γ) wk (` ze) (⇑ (σ ∷ Γ) σ ((` ze) , (` ze))))
... | (t , nt) = (ƛ t) , (ƛ nt)

⇑ Γ Ans (n , nn) = n , ((‘ nn) , refl)
⇑ Γ 𝟙 n = `nil
⇑ Γ (σ ẋ τ) (n , nn) = ⇑ Γ σ (π₁ n , π₁ nn) , ⇑ Γ τ (π₂ n , π₂ nn)
⇑ Γ (σ ⇒ τ) (n , nn) Θ ρ a u = {!  !} -- ⇑ Θ τ {!   !} -- ((rename ρ n · pr₁ (⇓ Θ σ u)) , {!   !})
 