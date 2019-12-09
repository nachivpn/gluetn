module Lib where

open import Data.Nat
  using (ℕ ; zero ; suc) public
open import Data.Unit
  using (⊤ ; tt) public
open import Data.Empty
  using (⊥ ; ⊥-elim) public
open import Data.Product
  using (∃ ; ∃₂ ; Σ ; _×_ ; _,_)
  renaming (proj₁ to π₁ ; proj₂ to π₂) public
open import Relation.Nullary
  using (¬_) public
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; subst)
  renaming (refl to ≡-refl ; trans to ≡-trans ; sym to ≡-sym) public
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans) public
open import Relation.Binary.Construct.Closure.Equivalence
  using (EqClosure ; symmetric)
  renaming (isEquivalence to EqClosureIsEquivalence) public
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂) public
open import Data.Sum
  using ()
  renaming (inj₁ to fwd ; inj₂ to bwd) public

open Star renaming (ε to refl) public
