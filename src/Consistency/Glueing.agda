----------------------------------------------
-- Proof of consistency using a glued model --
----------------------------------------------

module Consistency.Glueing where

open import Lib
open import CLT
open import Norm

private
  variable
    a b c : Ty

-- a "submodel" (called glued model) equipped with a proof
-- that quot is homomorphic on the reduction relation _⟶*_
-- Note: this submodel acts as *necessary* technical device
-- to prove consistency (see below)
Gl : ⟦ a ⟧ → Set
Gl {Nat}   n = ⊤
Gl {a ⇒ b} f = ∀ (x : ⟦ a ⟧) → Gl x
  → (quot f ∙ quot x ⟶* quot (f ∙' x))
  × Gl (f ∙' x)
Gl {a + b} (inj₁ x) = Gl x
Gl {a + b} (inj₂ y) = Gl y

-- application for glued values
appg : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
  → Gl f → Gl x
  → Gl (f ∙' x)
appg fg xg = π₂ (fg _ xg)

-- primitive recursion for glued values
recg : {x : ⟦ a ⟧} {f :  ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
  → Gl x → Gl f → Gl n → Gl (rec' x f n)
recg {n = zero}  xg fg ng = xg
recg {n = suc n} xg fg ng =
  appg (appg fg ng) (recg {n = n} xg fg ng)

caseg : {f : ⟦ a ⇒ c ⟧} → {g : ⟦ b ⇒ c ⟧} → {s : ⟦ a + b ⟧}
  → Gl f → Gl g → Gl s → Gl (case' f g s)
caseg {s = inj₁ x} fg gg sg = appg fg sg
caseg {s = inj₂ y} fg gg sg = appg gg sg

-- homomorphism properties of quot

hom-app : {f : ⟦ a ⇒ b ⟧} {x : ⟦ a ⟧}
  → Gl f → Gl x
  → quot f ∙ quot x ⟶* quot (f ∙' x)
hom-app fg xg = π₁ (fg _ xg)

hom-rec : {x : ⟦ a ⟧} {f : ⟦ Nat ⇒ a ⇒ a ⟧ } {n : ⟦ Nat ⟧}
    → Gl x → Gl f → Gl n
    → quot (eval Rec ∙' x ∙' f) ∙ quot n
    ⟶* quot (rec' x f n)
hom-rec {n = zero}  xg fg ng = lift rec0
hom-rec {x = x} {f} {n = suc n} xg fg ng =
      recs ◅ trans
        (app* (hom-app fg ng) (hom-rec {n = n} xg fg _))
        (hom-app (appg fg _) (recg {n = n} xg fg _))

hom-case : {f : ⟦ a ⇒ c ⟧ } {g : ⟦ b ⇒ c ⟧} {s : ⟦ a + b ⟧}
    → Gl f → Gl g → Gl s
    → quot (eval Case ∙' f ∙' g) ∙ quot s
    ⟶* quot (case' f g s)
hom-case {s = inj₁ x} fg gg sg = trans (lift redl) (hom-app fg sg)
hom-case {s = inj₂ y} fg gg sg = trans (lift redr) (hom-app gg sg)

open import Function

-- interpretation of terms in the glued model
-- Note: main challenge here is to provide a proof
-- object that quot is a homomorphism in each case
gl : (t : Tm a) →  Gl (eval t)
gl K x xg    = refl , λ x _ → (lift redk) , xg
gl Zero      = tt
gl Succ      = λ x _ → refl , tt
gl (t ∙ u) = π₂ (gl t _ (gl u))
gl S g gg    = refl , λ f fg →
  refl , λ x xg →
       reds ◅ trans
         (app* (hom-app gg xg) (hom-app fg xg))
         (hom-app (appg gg xg) (appg fg xg))
      , appg (appg gg xg) (appg fg xg)
gl Rec x xg   = refl , (λ f fg →
  refl , λ n ng →
    hom-rec {n = n} xg fg ng , (recg {n = n} xg fg ng))
gl Inl x xg = refl , xg
gl Inr x xg = refl , xg
gl (Case) f fg = refl , λ g gg →
  refl , λ s sg → hom-case {s = s} fg gg sg , caseg {s = s} fg gg sg

-- normalization is consistent with reduction (_⟶*_)
-- or, loosely speaking, `norm` transforms by reduction
consistent-red* : (t : Tm a) → t ⟶* em (norm t)
consistent-red* K = refl
consistent-red* S = refl
consistent-red* Zero = refl
consistent-red* Succ = refl
consistent-red* Rec = refl
consistent-red* (t ∙ u) = trans
  (app* (consistent-red* t) (consistent-red* u))
  (hom-app (gl t) (gl u))
consistent-red* Inl  = refl
consistent-red* Inr  = refl
consistent-red* Case = refl

-- normalization is consistent with conversion
consistent : (t : Tm a) → t ≈ em (norm t)
consistent t = ⟶*→≈ (consistent-red* t)
