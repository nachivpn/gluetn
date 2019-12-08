module Soundness where

open import Lib
open import CLT
open import Norm

private
  variable
    a b c : Ty

-- soundness of reduction in the model
sound-red : {t t' : Tm a} → t ⟶ t' → eval t ≡ eval t'
sound-red redk = ≡-refl
sound-red reds = ≡-refl
sound-red rec0 = ≡-refl
sound-red recs = ≡-refl
sound-red (app1 p)
  = cong (λ x → x ∙' _) (sound-red p)
sound-red (app2 {t = t} p)
  = cong (λ x → (eval t) ∙' x) (sound-red p)
sound-red redl = ≡-refl
sound-red redr = ≡-refl
sound-red (inl p)
  = cong inj₁ (sound-red p)
sound-red (inr p)
  = cong inj₂ (sound-red p)

-- soundness of conversion in the model
sound : {t t' : Tm a} → t ≈ t' → eval t ≡ eval t'
sound refl = ≡-refl
sound (fwd x ◅ p) = ≡-trans (sound-red x) (sound p)
sound (bwd y ◅ p) = ≡-trans (≡-sym (sound-red y)) (sound p)

-- convertible terms yield the same normal form
unique-nf-forth : {t t' : Tm a} → t ≈ t' → norm t ≡ norm t'
unique-nf-forth p = cong reify (sound p)
