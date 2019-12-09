----------------------------------------------------------
-- Interesting corollaries of the normalization theorem --
----------------------------------------------------------

module Corollaries where

open import Lib
open import CLT
open import Norm

open import Soundness using (sound)
open import Completeness using (unique-nf-back)

private
  variable
    a b c : Ty

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
stability Unit = ≡-refl
stability Init = ≡-refl

---------------------------------
-- Constructors are one-to-one --
---------------------------------

succ-o2o : {t u : Tm Nat}
  → Succ ∙ t ≈ Succ ∙ u
  → t ≈ u
succ-o2o p
  = unique-nf-back (cong reify (suc-o2o (sound p)))
  where
  -- suc is one-to-one in the semantics
  suc-o2o : {n m : ⟦ Nat ⟧}
    → suc n ≡ suc m
    → n ≡ m
  suc-o2o ≡-refl = ≡-refl

inl-o2o : {t u : Tm a}
  → Inl {a} {b} ∙ t ≈ Inl ∙ u
  → t ≈ u
inl-o2o p
  = unique-nf-back (cong reify (inj₁-o2o (sound p)))
  where
  -- inj₁ is one-to-one in the semantics
  inj₁-o2o : {x y : ⟦ a ⟧}
    → inj₁ {_} {_} {⟦ a ⟧} {⟦ b ⟧} x ≡ inj₁ y
    → x ≡ y
  inj₁-o2o ≡-refl = ≡-refl

-------------------------
-- Logical consistency --
-------------------------

log-consistency : ¬ (Tm 𝟘)
log-consistency t with (eval t)
log-consistency t | ()
