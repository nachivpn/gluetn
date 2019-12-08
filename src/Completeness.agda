module Completeness where

open import Lib
open import CLT
open import Norm
  using (eval ; reify ; norm)
open import Consistency.Glueing
  using (consistent)

private
  variable
    a b c : Ty

-- if the normal forms are two terms are equal,
-- then the terms must be convertible
unique-nf-back : {t t' : Tm a} → norm t ≡ norm t' → t ≈ t'
unique-nf-back {t = t} {t'} p =
  trans (consistent t) (trans (≡→≈ (cong em p)) (sym (consistent t')))

-- completeness of interpretation in the model
complete : {t t' : Tm a} → eval t ≡ eval t' → t ≈ t'
complete p = unique-nf-back (cong reify p)
