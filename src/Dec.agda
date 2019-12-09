module Dec where

open import CLT
open import Norm
open import Soundness
open import Completeness

open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; subst)
  renaming (refl to ≡-refl ; trans to ≡-trans ; sym to ≡-sym)

private
  variable
    a b c : Ty

-- syntactic equality of types is decidable
≡-ty-dec : Dec (a ≡ b)
-- (below)

-- syntactic equality of normal forms is decidable
≡-nf-dec : (n n' : Nf a) → Dec (n ≡ n')
-- (below)

---------------------------------------
-- convertibility of terms is decidable
---------------------------------------
≈-tm-dec : (t t' : Tm a) → Dec (t ≈ t')
≈-tm-dec t t' with (≡-nf-dec (norm t) (norm t'))
≈-tm-dec t t' | yes p = yes (unique-nf-back p)
≈-tm-dec t t' | no ¬p = no (λ { q → ¬p (unique-nf-forth q) })

-- Impl of ≡-ty-dec
≡-ty-dec {Nat} {Nat} = yes ≡-refl
≡-ty-dec {Nat} {b ⇒ b₁} = no (λ ())
≡-ty-dec {a ⇒ a₁} {Nat} = no (λ ())
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} with ≡-ty-dec {a} {b} | ≡-ty-dec {a₁} {b₁}
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | yes p | yes q = yes (cong₂ _⇒_ p q)
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | yes p | no ¬q = no (λ { ≡-refl → ¬q ≡-refl})
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | no ¬p | yes q = no (λ { ≡-refl → ¬p ≡-refl})
≡-ty-dec {a ⇒ a₁} {b ⇒ b₁} | no ¬p | no ¬q = no λ { ≡-refl → ¬q ≡-refl}
≡-ty-dec {Nat} {b + b₁} = no (λ ())
≡-ty-dec {a ⇒ a₁} {b + b₁} = no (λ ())
≡-ty-dec {a + a₁} {Nat} = no (λ ())
≡-ty-dec {a + a₁} {b ⇒ b₁} = no (λ ())
≡-ty-dec {a + a₁} {b + b₁} with ≡-ty-dec {a} {b} | ≡-ty-dec {a₁} {b₁}
≡-ty-dec {a + a₁} {b + b₁} | yes p | yes q = yes (cong₂ _+_ p q)
≡-ty-dec {a + a₁} {b + b₁} | yes p | no ¬q = no (λ { ≡-refl → ¬q ≡-refl})
≡-ty-dec {a + a₁} {b + b₁} | no ¬p | yes q = no (λ { ≡-refl → ¬p ≡-refl})
≡-ty-dec {a + a₁} {b + b₁} | no ¬p | no ¬q = no (λ { ≡-refl → ¬q ≡-refl})
≡-ty-dec {𝟘} {𝟘} = yes ≡-refl
≡-ty-dec {𝟘} {𝟙} = no (λ ())
≡-ty-dec {𝟘} {Nat} = no (λ ())
≡-ty-dec {𝟘} {b ⇒ b₁} = no (λ ())
≡-ty-dec {𝟘} {b + b₁} = no (λ ())
≡-ty-dec {𝟙} {𝟘} = no (λ ())
≡-ty-dec {𝟙} {𝟙} = yes ≡-refl
≡-ty-dec {𝟙} {Nat} = no (λ ())
≡-ty-dec {𝟙} {b ⇒ b₁} = no (λ ())
≡-ty-dec {𝟙} {b + b₁} = no (λ ())
≡-ty-dec {Nat} {𝟘} = no (λ ())
≡-ty-dec {Nat} {𝟙} = no (λ ())
≡-ty-dec {a ⇒ a₁} {𝟘} = no (λ ())
≡-ty-dec {a ⇒ a₁} {𝟙} = no (λ ())
≡-ty-dec {a + a₁} {𝟘} = no (λ ())
≡-ty-dec {a + a₁} {𝟙} = no (λ ())

-- Impl of ≡-nf-dec
≡-nf-dec Zero Zero = yes ≡-refl
≡-nf-dec Zero (Succ∙ n') = no (λ ())
≡-nf-dec Succ Succ = yes ≡-refl
≡-nf-dec Succ (K∙ n') = no (λ ())
≡-nf-dec Succ (S∙∙ n' n'') = no (λ ())
≡-nf-dec Succ (Rec∙∙ n' n'') = no (λ ())
≡-nf-dec (Succ∙ n) Zero = no (λ ())
≡-nf-dec (Succ∙ n) (Succ∙ n') with (≡-nf-dec n n')
... | yes p = yes (cong Succ∙ p)
... | no ¬p = no λ { ≡-refl → ¬p ≡-refl}
≡-nf-dec K K = yes ≡-refl
≡-nf-dec K (K∙ n') = no (λ ())
≡-nf-dec K (S∙ n') = no (λ ())
≡-nf-dec K (S∙∙ n' n'') = no (λ ())
≡-nf-dec K (Rec∙∙ n' n'') = no (λ ())
≡-nf-dec (K∙ n) Succ = no (λ ())
≡-nf-dec (K∙ n) K = no (λ ())
≡-nf-dec (K∙ n) (K∙ n') with (≡-nf-dec n n')
... | yes p = yes (cong K∙ p )
... | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
≡-nf-dec (K∙ n) S = no (λ ())
≡-nf-dec (K∙ n) (S∙ n') = no (λ ())
≡-nf-dec (K∙ n) (S∙∙ n' n'') = no (λ ())
≡-nf-dec (K∙ n) Rec = no (λ ())
≡-nf-dec (K∙ n) (Rec∙ n') = no (λ ())
≡-nf-dec (K∙ n) (Rec∙∙ n' n'') = no (λ ())
≡-nf-dec S (K∙ n') = no (λ ())
≡-nf-dec S S = yes ≡-refl
≡-nf-dec S (S∙∙ n' n'') = no (λ ())
≡-nf-dec (S∙ n) K = no (λ ())
≡-nf-dec (S∙ n) (K∙ n') = no (λ ())
≡-nf-dec (S∙ n) (S∙ n') with (≡-nf-dec n n')
... | yes p = yes (cong S∙ p )
... | no ¬p = no λ {  ≡-refl → ¬p ≡-refl }
≡-nf-dec (S∙ n) (S∙∙ n' n'') = no (λ ())
≡-nf-dec (S∙ n) (Rec∙ n') = no (λ ())
≡-nf-dec (S∙∙ n n₁) Succ = no (λ ())
≡-nf-dec (S∙∙ n n₁) K = no (λ ())
≡-nf-dec (S∙∙ n n₁) (K∙ n') = no (λ ())
≡-nf-dec (S∙∙ n n₁) S = no (λ ())
≡-nf-dec (S∙∙ n n₁) (S∙ n') = no (λ ())
≡-nf-dec (S∙∙ {b = b} n m) (S∙∙ {b = b'} n' m') with ≡-ty-dec {b} {b'}
... | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
... | yes ≡-refl with (≡-nf-dec n n') | (≡-nf-dec m m')
... | yes q | yes r = yes (cong₂ S∙∙ q r)
... | yes q | no ¬r = no λ { ≡-refl → ¬r ≡-refl }
... | no ¬q | r = no λ { ≡-refl → ¬q ≡-refl }
≡-nf-dec (S∙∙ n n₁) Rec = no (λ ())
≡-nf-dec (S∙∙ n n₁) (Rec∙ n') = no (λ ())
≡-nf-dec (S∙∙ n n₁) (Rec∙∙ n' n'') = no (λ ())
≡-nf-dec Rec (K∙ n') = no (λ ())
≡-nf-dec Rec (S∙∙ n' n'') = no (λ ())
≡-nf-dec Rec Rec = yes ≡-refl
≡-nf-dec Rec (Rec∙∙ n' n'') = no (λ ())
≡-nf-dec (Rec∙ n) (K∙ n') = no (λ ())
≡-nf-dec (Rec∙ n) (S∙ n') = no (λ ())
≡-nf-dec (Rec∙ n) (S∙∙ n' n'') = no (λ ())
≡-nf-dec (Rec∙ n) (Rec∙ n') with (≡-nf-dec n n')
≡-nf-dec (Rec∙ n) (Rec∙ n') | yes p = yes (cong Rec∙ p)
≡-nf-dec (Rec∙ n) (Rec∙ n') | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
≡-nf-dec (Rec∙∙ n n₁) Succ = no (λ ())
≡-nf-dec (Rec∙∙ n n₁) K = no (λ ())
≡-nf-dec (Rec∙∙ n n₁) (K∙ n') = no (λ ())
≡-nf-dec (Rec∙∙ n n₁) (S∙∙ n' n'') = no (λ ())
≡-nf-dec (Rec∙∙ n n₁) Rec = no (λ ())
≡-nf-dec (Rec∙∙ n m) (Rec∙∙ n' m') with (≡-nf-dec n n') | (≡-nf-dec m m')
... | yes p | yes q = yes (cong₂ Rec∙∙ p q)
... | yes p | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
... | no ¬p | _     = no λ { ≡-refl → ¬p ≡-refl }
≡-nf-dec K (Case∙∙ n' n'') = no (λ ())
≡-nf-dec (K∙ n) Inl = no (λ ())
≡-nf-dec (K∙ n) Inr = no (λ ())
≡-nf-dec (K∙ n) Case = no (λ ())
≡-nf-dec (K∙ n) (Case∙ n') = no (λ ())
≡-nf-dec (K∙ n) (Case∙∙ n' n'') = no (λ ())
≡-nf-dec (S∙ n) Case = no (λ ())
≡-nf-dec (S∙∙ n n₁) Inl = no (λ ())
≡-nf-dec (S∙∙ n n₁) Inr = no (λ ())
≡-nf-dec (S∙∙ n n₁) Case = no (λ ())
≡-nf-dec (S∙∙ n n₁) (Case∙ n') = no (λ ())
≡-nf-dec (S∙∙ n n₁) (Case∙∙ n' n'') = no (λ ())
≡-nf-dec Rec (Case∙∙ n' n'') = no (λ ())
≡-nf-dec (Rec∙∙ n n₁) Inl = no (λ ())
≡-nf-dec (Rec∙∙ n n₁) Inr = no (λ ())
≡-nf-dec Inl (K∙ n') = no (λ ())
≡-nf-dec Inl (S∙∙ n' n'') = no (λ ())
≡-nf-dec Inl (Rec∙∙ n' n'') = no (λ ())
≡-nf-dec Inl Inl = yes ≡-refl
≡-nf-dec Inl Inr = no (λ ())
≡-nf-dec Inl (Case∙∙ n' n'') = no (λ ())
≡-nf-dec Inr (K∙ n') = no (λ ())
≡-nf-dec Inr (S∙∙ n' n'') = no (λ ())
≡-nf-dec Inr (Rec∙∙ n' n'') = no (λ ())
≡-nf-dec Inr Inl = no (λ ())
≡-nf-dec Inr Inr = yes ≡-refl
≡-nf-dec Inr (Case∙∙ n' n'') = no (λ ())
≡-nf-dec (Inl∙ n) (Inl∙ n') with (≡-nf-dec n n')
... | yes p = yes (cong Inl∙ p)
... | no ¬p = no  λ { ≡-refl → ¬p ≡-refl }
≡-nf-dec (Inl∙ n) (Inr∙ n') = no (λ ())
≡-nf-dec (Inr∙ n) (Inl∙ n') = no (λ ())
≡-nf-dec (Inr∙ n) (Inr∙ n') with (≡-nf-dec n n')
... | yes p = yes (cong Inr∙ p)
... | no ¬p = no  λ { ≡-refl → ¬p ≡-refl }
≡-nf-dec Case (K∙ n') = no (λ ())
≡-nf-dec Case (S∙ n') = no (λ ())
≡-nf-dec Case (S∙∙ n' n'') = no (λ ())
≡-nf-dec Case Case = yes ≡-refl
≡-nf-dec (Case∙ n) (K∙ n') = no (λ ())
≡-nf-dec (Case∙ n) (S∙∙ n' n'') = no (λ ())
≡-nf-dec (Case∙ n) (Case∙ n') with (≡-nf-dec n n')
... | yes p = yes (cong Case∙ p)
... | no ¬p = no  λ { ≡-refl → ¬p ≡-refl }
≡-nf-dec (Case∙∙ n n₁) K = no (λ ())
≡-nf-dec (Case∙∙ n n₁) (K∙ n') = no (λ ())
≡-nf-dec (Case∙∙ n n₁) (S∙∙ n' n'') = no (λ ())
≡-nf-dec (Case∙∙ n n₁) Rec = no (λ ())
≡-nf-dec (Case∙∙ n n₁) Inl = no (λ ())
≡-nf-dec (Case∙∙ n n₁) Inr = no (λ ())
≡-nf-dec (Case∙∙ n m) (Case∙∙ n' m') with (≡-nf-dec n n') | (≡-nf-dec m m')
... | yes p | yes q = yes (cong₂ Case∙∙ p q)
... | yes p | no ¬p = no λ { ≡-refl → ¬p ≡-refl }
... | no ¬p | _     = no λ { ≡-refl → ¬p ≡-refl }
≡-nf-dec K Init = no (λ ())
≡-nf-dec (K∙ n) Init = no (λ ())
≡-nf-dec (S∙∙ n n₁) Init = no (λ ())
≡-nf-dec Rec Init = no (λ ())
≡-nf-dec Inl Init = no (λ ())
≡-nf-dec Inr Init = no (λ ())
≡-nf-dec Unit Unit = yes ≡-refl
≡-nf-dec Init K = no (λ ())
≡-nf-dec Init (K∙ m) = no (λ ())
≡-nf-dec Init (S∙∙ m m₁) = no (λ ())
≡-nf-dec Init Rec = no (λ ())
≡-nf-dec Init Inl = no (λ ())
≡-nf-dec Init Inr = no (λ ())
≡-nf-dec Init Init = yes ≡-refl
