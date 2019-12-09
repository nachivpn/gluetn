----------------------------------------------------------
-- Types, terms, reduction, conversion and normal forms --
----------------------------------------------------------

module CLT where

open import Lib

open import Data.Sum
  using ()
  renaming (inj₁ to fwd ; inj₂ to bwd)

infixl 6 _+_
infixr 5 _⇒_

data Ty : Set where
  𝟘 𝟙 : Ty
  Nat : Ty
  _⇒_ _+_ : Ty →  Ty → Ty

private
  variable
    a b c : Ty

infixl 5 _∙_

-- Combinatory version of System T
data Tm : Ty → Set where
  K    : Tm (a ⇒ b ⇒ a)
  S    : Tm ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  Zero : Tm Nat
  Succ : Tm (Nat ⇒ Nat)
  Rec  : Tm (a ⇒ (Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  _∙_  : Tm (a ⇒ b) → Tm a → Tm b
  Inl  : Tm (a ⇒ a + b)
  Inr  : Tm (b ⇒ a + b)
  Case : Tm ((a ⇒ c) ⇒ (b ⇒ c) ⇒ (a + b) ⇒ c)
  Init : Tm (𝟘 ⇒ a)
  Unit : Tm 𝟙

-- NOTE: The presentation of System T here takes after a
-- Hilbert-style proof system for intuitionistic propositional logic
-- with axioms (K, S, etc.,) and a single inference rule (_∙_)

-- small-step reduction relation
data _⟶_ : Tm a → Tm a → Set where
  redk : {e : Tm a} {e' : Tm b}
     → (K ∙ e ∙ e') ⟶ e
  reds : {g : Tm (a ⇒ b ⇒ c)} {f : Tm (a ⇒ b)} {e : Tm a}
     → (S ∙ g ∙ f ∙ e) ⟶ (g ∙ e ∙ (f ∙ e))
  rec0 : {e : Tm a} {f : Tm (Nat ⇒ a ⇒ a)}
     → (Rec ∙ e ∙ f ∙ Zero) ⟶ e
  recs : {e : Tm a} {f : Tm (Nat ⇒ a ⇒ a)} {n : Tm Nat}
     → (Rec ∙ e ∙ f ∙ (Succ ∙ n)) ⟶ (f ∙ n ∙ (Rec ∙ e ∙ f ∙ n))
  app1  : {t t' : Tm (a ⇒ b)} {u : Tm a}
    → t ⟶ t'
    → (t ∙ u) ⟶ (t' ∙ u)
  app2  : {t : Tm (a ⇒ b)} {u u' : Tm a}
    → u ⟶ u'
    → (t ∙ u) ⟶ (t ∙ u')
  redl : {s : Tm a} {f : Tm (a ⇒ c)} {g : Tm (b ⇒ c)}
    → (Case ∙ f ∙ g ∙ (Inl ∙ s)) ⟶ (f ∙ s)
  redr : {s : Tm b} {f : Tm (a ⇒ c)} {g : Tm (b ⇒ c)}
    → (Case ∙ f ∙ g ∙ (Inr ∙ s)) ⟶ (g ∙ s)

-- NOTE: The relation _⟶_ is *not* deterministic
-- since we can make a choice when we encounter `App`

infix 3 _⟶*_

-- zero or more steps of reduction
_⟶*_ : Tm a → Tm a → Set
_⟶*_ = Star (_⟶_)

infix 3 _≈_

-- conversion relation built from reduction steps,
-- yields an equational theory for terms
_≈_    : Tm a → Tm a → Set
_≈_   = EqClosure _⟶_

data Nf : Ty → Set where
  -- nats
  Zero  : Nf Nat
  Succ  : Nf (Nat ⇒ Nat)
  Succ∙ : (n : Nf Nat) → Nf Nat
  -- K-terms
  K     : Nf (a ⇒ b ⇒ a)
  K∙    : (n : Nf a) → Nf (b ⇒ a)
  -- S-terms
  S     : Nf ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  S∙    : (n : Nf (a ⇒ b ⇒ c)) → Nf ((a ⇒ b) ⇒ a ⇒ c)
  S∙∙   : (m : Nf (a ⇒ b ⇒ c)) → (n : Nf (a ⇒ b)) → Nf (a ⇒ c)
  -- Rec-terms
  Rec   : Nf (a ⇒ (Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  Rec∙  : (n : Nf a) → Nf ((Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  Rec∙∙ : (m : Nf a) → (n : Nf (Nat ⇒ a ⇒ a)) → Nf (Nat ⇒ a)
  -- In*-terms
  Inl    : Nf (a ⇒ a + b)
  Inr    : Nf (b ⇒ a + b)
  Inl∙   : Nf a → Nf (a + b)
  Inr∙   : Nf b → Nf (a + b)
  -- Case-terms
  Case   : Nf ((a ⇒ c) ⇒ (b ⇒ c) ⇒ (a + b) ⇒ c)
  Case∙  : Nf (a ⇒ c) → Nf ((b ⇒ c) ⇒ (a + b) ⇒ c)
  Case∙∙ : Nf (a ⇒ c) → Nf (b ⇒ c) → Nf (a + b ⇒ c)
  -- Unit and Init
  Unit   : Nf 𝟙
  Init   : Nf (𝟘 ⇒ a)

-- embed normal forms to terms
em : Nf a → Tm a
em Zero         = Zero
em Succ         = Succ
em (Succ∙ n)    = Succ ∙ em n
em K            = K
em (K∙ n)       = K ∙ (em n)
em S            = S
em (S∙ n)       = S ∙ (em n)
em (S∙∙ m n)    = S ∙ (em m) ∙ (em n)
em Rec          = Rec
em (Rec∙ n)     = Rec ∙ (em n)
em (Rec∙∙ m n)  = Rec ∙ (em m) ∙ (em n)
em Inl          = Inl
em Inr          = Inr
em (Inl∙ n)     = Inl ∙ em n
em (Inr∙ n)     = Inr ∙ em n
em Case         = Case
em (Case∙ n)    = Case ∙ (em n)
em (Case∙∙ m n) = Case ∙ (em m) ∙ (em n)
em Unit         = Unit
em Init         = Init

module Utilities where

  sym : {t t' : Tm a} → t ≈ t' → t' ≈ t
  sym = symmetric _⟶_

  -- embed reduction relations into ≈

  ⟶→≈ : {e e' : Tm a}
    → e ⟶ e'
    → e ≈ e'
  ⟶→≈ p = fwd p ◅ refl

  ⟶*→≈ : {t u : Tm a} → t ⟶* u → t ≈ u
  ⟶*→≈ refl = refl
  ⟶*→≈ (x ◅ p) = trans (⟶→≈ x) (⟶*→≈ p)

  -- embed ⟶ to ⟶*
  lift : {e e' : Tm a}
    → e ⟶ e'
    → e ⟶* e'
  lift p = p ◅ refl

  -- congruence rule for ∙ (in ⟶*)
  app*  : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
      → t ⟶* t'
      → u ⟶* u'
      → t ∙ u ⟶* t' ∙ u'
  app* refl    refl    = refl
  app* refl    (x ◅ q) = (app2 x) ◅ (app* refl q)
  app* (x ◅ p) q       = (app1 x) ◅ (app* p q)

  -- congruence rule for ∙ (in ≈)
  app : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
    → t ≈ t'
    → u ≈ u'
    → t ∙ u ≈ t' ∙ u'
  app refl refl = refl
  app refl (fwd x ◅ q) = fwd (app2 x) ◅ app refl q
  app refl (bwd y ◅ q) = bwd (app2 y) ◅ app refl q
  app (fwd x ◅ p) refl = fwd (app1 x) ◅ app p refl
  app (bwd y ◅ p) refl = bwd (app1 y) ◅ app p refl
  app (fwd x ◅ p) (fwd y ◅ q)
    = trans (fwd (app1 x) ◅ fwd (app2 y) ◅ refl) (app p q)
  app (fwd x ◅ p) (bwd y ◅ q)
    = trans (fwd (app1 x) ◅ bwd (app2 y) ◅ refl) (app p q)
  app (bwd x ◅ p) (fwd y ◅ q)
    = trans (bwd (app1 x) ◅ fwd (app2 y) ◅ refl) (app p q)
  app (bwd x ◅ p) (bwd y ◅ q)
    = trans (bwd (app1 x) ◅ bwd (app2 y) ◅ refl) (app p q)

  -- syntactically identical terms are convertible
  ≡→≈ : {t t' : Tm a} → t ≡ t' → t ≈ t'
  ≡→≈ ≡-refl = refl

open Utilities public

module SetoidUtil where

  open import Relation.Binary
    using (Setoid ; IsEquivalence)

  open Setoid
    renaming (_≈_ to _≈ₑ_)
    using (Carrier ; isEquivalence)

  -- Terms form a setoid
  Tms : (a : Ty) → Setoid _ _
  Tms a .Carrier = Tm a
  Tms a ._≈ₑ_     = _≈_
  Tms a .isEquivalence = EqClosureIsEquivalence _⟶_

  open import Relation.Binary.SetoidReasoning public

open SetoidUtil public
