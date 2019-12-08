--------------------------------
-- Normalization construction --
--------------------------------

module Norm where

open import Lib
open import CLT

private
  variable
    a b c : Ty

-- interpretation of types in the model
⟦_⟧ : Ty → Set
⟦  Nat  ⟧ = ℕ
⟦ a ⇒ b ⟧ = Nf (a ⇒ b) × (⟦ a ⟧ → ⟦ b ⟧)
⟦ a + b ⟧ = ⟦ a ⟧ ⊎ ⟦ b ⟧

-- reify values in the model to normal forms
reify : ⟦ a ⟧ → Nf a
reify {Nat}   zero     = Zero
reify {Nat}   (suc x)  = Succ∙ (reify x)
reify {a ⇒ b} (t , _)  = t
reify {a + b} (inj₁ x) = Inl∙ (reify x)
reify {a + b} (inj₂ y) = Inr∙ (reify y)

-- "quote" values in the model into terms
-- p.s. cannot be named "quote" since it's an Agda keyword
quot : ⟦ a ⟧ → Tm a
quot v = em (reify v)

infixl 5 _∙'_

-- semantic application
_∙'_ : ⟦ a ⇒ b ⟧ → ⟦ a ⟧ → ⟦ b ⟧
_∙'_ (_ , f) x = f x

-- semantic recursion
rec' : ⟦ a ⟧ → ⟦ Nat ⇒ a ⇒ a ⟧ → ⟦ Nat ⟧ → ⟦ a ⟧
rec' b f zero = b
rec' b f (suc n) = f ∙' n ∙' (rec' b f n)

-- semantic case
case' : ⟦ a ⇒ c ⟧ → ⟦ b ⇒ c ⟧ → ⟦ a + b ⟧ → ⟦ c ⟧
case' f g (inj₁ x) = f ∙' x
case' f g (inj₂ y) = g ∙' y

-- interpretation of terms in the model
eval : Tm a → ⟦ a ⟧
eval K    = K , λ x → (K∙ (reify x)) , λ _ → x
eval S    = S , λ g →
  S∙ (reify g) , λ f →
    S∙∙ (reify g) (reify f) , λ x →
      (g ∙' x) ∙' (f ∙' x)
eval Zero = zero
eval Succ = Succ , suc
eval Rec  = Rec , λ b →
  Rec∙ (reify b) , λ f  →
    Rec∙∙ (reify b) (reify f) , λ n →
      rec' b f n
eval (t ∙ u) = (eval t) ∙' (eval u)
eval Inl = Inl , inj₁
eval Inr = Inr , inj₂
eval (Case)  = Case , λ f →
  Case∙ (reify f) , λ g →
    Case∙∙ (reify f) (reify g) , λ s →
      case' f g s

-- normalization function
norm : Tm a → Nf a
norm t = reify (eval t)

-- norm is idempotent on normal forms
stability : (n : Nf a) → norm (em n) ≡ n
stability Zero = ≡-refl
stability Succ = ≡-refl
stability (Succ∙ n) = cong Succ∙ (stability n)
stability K = ≡-refl
stability (K∙ n) = cong K∙ (stability n)
stability S = ≡-refl
stability (S∙ n) = cong S∙ (stability n)
stability (S∙∙ m n) = cong₂ S∙∙ (stability m) (stability n)
stability Rec = ≡-refl
stability (Rec∙ n) = cong Rec∙ (stability n)
stability (Rec∙∙ m n) = cong₂ Rec∙∙ (stability m) (stability n)
stability Inl = ≡-refl
stability Inr = ≡-refl
stability (Inl∙ n) = cong Inl∙ (stability n)
stability (Inr∙ n) = cong Inr∙ (stability n)
stability Case = ≡-refl
stability (Case∙ n) = cong Case∙ (stability n)
stability (Case∙∙ m n) = cong₂ Case∙∙ (stability m) (stability n)
