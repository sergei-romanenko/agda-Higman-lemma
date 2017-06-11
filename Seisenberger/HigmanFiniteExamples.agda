module HigmanFiniteExamples where

open import Data.Nat as Nat
  using (ℕ; zero; suc)
open import Data.List as List
  hiding (any; all)
open import Data.List.All as All
  using (All; []; _∷_)
open import Data.List.Any as Any
  using (Any; here; there; any; module Membership; module Membership-≡)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃₂; uncurry)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using(⊥; ⊥-elim)

open import Function
import Function.Related as Related

open import Relation.Nullary
open import Relation.Binary
  using (Rel; Decidable)
open import Relation.Binary.PropositionalEquality as P
  renaming([_] to ≡[_])

module Bar-[]→Bar-ws
  (Letter : Set)
  (_≟_ : (a b : Letter) → Dec (a ≡ b))
  where

  open import HigmanFinite Letter _≟_

  -- Bar [] → ∀ ws → Bar ws

  bar[]→∀bar-w : ∀ vs → Bar vs → ∀ w → Bar (w ∷ vs)
  bar[]→∀bar-w vs (now g) w = now (good-later g)
  bar[]→∀bar-w vs (later l) w = later (bar[]→∀bar-w (w ∷ vs) (l w))

  bar[]→∀bar-ws : ∀ vs → Bar vs → ∀ ws → Bar (ws ++ vs)
  bar[]→∀bar-ws vs bar-vs [] = bar-vs
  bar[]→∀bar-ws vs bar-vs (w ∷ ws) =
    bar[]→∀bar-w (ws ++ vs) (bar[]→∀bar-ws vs bar-vs ws) w

  bar[]→∀bar : Bar [] → ∀ ws → Bar ws
  bar[]→∀bar bar[] ws =
    subst Bar (++[]≡ ws) (bar[]→∀bar-ws [] bar[] ws)
    where ++[]≡ : ∀ us → us ++ [] ≡ us
          ++[]≡ [] = refl
          ++[]≡ (u ∷ us) = cong (_∷_ u) (++[]≡ us)


module SequencesAsFunctions
  (Letter : Set)
  (_≟_ : (a b : Letter) → Dec (a ≡ b))
  where

  open import HigmanFinite Letter _≟_

  -- f // n constructs the list f (n - 1) ∷ ... ∷ f 0 ∷ [] .

  _//_ : ∀ {ℓ} {A : Set ℓ} (f : ℕ → A) (n : ℕ) → List A
  f // zero = []
  f // suc n = (f n) ∷ (f // n)

  -- If Bar [] , then, eventually, (f // m) becomes good.

  bar//→good// : ∀ (f : ℕ → Word) (n : ℕ)→ Bar (f // n) →
    ∃ λ m → Good (f // m)
  bar//→good// f n (now g) = n , g
  bar//→good// f n (later l) =
    bar//→good// f (suc n) (l (f n))

  bar[]→good// : ∀ (f : ℕ → Word) → Bar [] →
    ∃ λ m → Good (f // m)
  bar[]→good// f bar[] =
    bar//→good// f zero bar[]

module Higman⊥ where

  open import Data.Empty

  _≟⊥_ : Decidable {A = ⊥} _≡_
  () ≟⊥ ()

  import HigmanFinite as H
  open H ⊥ _≟⊥_

  barW[] : BarW []
  barW[] = barW-later (λ ())

  higman⊥ : Bar []
  higman⊥ = higman barW[]

  mutual

    hg⊥ : Bar []
    hg⊥ = later hg⊥₁

    hg⊥₁ : ∀ w → Bar (w ∷ [])
    hg⊥₁ [] = bar[]∷ []
    hg⊥₁ (() ∷ w)

module Higman⊤ where

  open import Data.Unit

  _≟⊤_ : Decidable {A = ⊤} _≡_
  tt ≟⊤ tt = yes refl

  import HigmanFinite as H
  open H ⊤ _≟⊤_

  mutual

    barW[] : BarW []
    barW[] = barW-later barW[]₁

    barW[]₁ : ∀ a → BarW (a ∷ [])
    barW[]₁ tt = barW-later barW[]₂

    barW[]₂ : ∀ b → BarW (b ∷ tt ∷ [])
    barW[]₂ tt = barW-now (goodW-now (here refl))
  
  higman⊤ : Bar []
  higman⊤ = higman barW[]

 
module HigmanBool where

  open import Data.Bool
    renaming (_≟_ to _≟Bool_)

  import HigmanFinite as H
  open H Bool _≟Bool_

  mutual

    barW[] : BarW []
    barW[] = barW-later barW₀

    barW₀ : ∀ a → BarW (a ∷ [])
    barW₀ true = barW-later barWt
    barW₀ false = barW-later barWf

    barWt : ∀ a → BarW (a ∷ true ∷ [])
    barWt true = barW-now (goodW-now (here refl))
    barWt false = barW-later barWft

    barWft : ∀ a → BarW (a ∷ false ∷ true ∷ [])
    barWft true = barW-now (goodW-now (there (here refl)))
    barWft false = barW-now (goodW-now (here refl))

    barWf : ∀ a → BarW (a ∷ false ∷ [])
    barWf true = barW-later barWtf
    barWf false = barW-now (goodW-now (here refl))

    barWtf : ∀ a → BarW (a ∷ true ∷ false ∷ [])
    barWtf true = barW-now (goodW-now (here refl))
    barWtf false = barW-now (goodW-now (there (here refl)))

  higmanBool : Bar []
  higmanBool = higman barW[]

module HigmanFin (n : ℕ) where

  open import Data.Fin
  open import Data.Fin.Properties
    using (_≟_)

  open import Relation.Binary
    using (IsDecEquivalence; DecSetoid)

  import Data.Vec as Vec
  import Data.List.Countdown as Countdown

  import HigmanFinite as H
  open H (Fin n) (_≟_ {n})

  -- The first, naive attempt.
  -- The type of the function is correct, but it fails to pass
  -- the termination check.
  -- We need to add a "decreasing" argument!

  {-# NON_TERMINATING #-}
  barW₀-bad : ∀ a as → BarW (a ∷ as)
  barW₀-bad a as with a ∈? as
  ... | yes a∈as = barW-now (goodW-now a∈as)
  ... | no  a∉as = barW-later (λ b → barW₀-bad b (a ∷ as))

  barW[]-bad : BarW []
  barW[]-bad = barW-later (λ a → barW₀-bad a [])

  -- The countdown data structure can be used to keep track of (an upper
  -- bound of) the number of available fresh letters.

  isDecEquivalence : IsDecEquivalence _≡_
  isDecEquivalence = DecSetoid.isDecEquivalence (P.decSetoid (_≟_ {n}))

  open  Countdown (record { isDecEquivalence = isDecEquivalence })

  allFinList : List (Fin n)
  allFinList = Vec.toList (Vec.allFin n)

  []⊕n : [] ⊕ n
  []⊕n = empty (record { to = record { _⟨$⟩_ = id; cong = id}; injective = id})

  -- Now k counts the number of remaining fresh letters.

  barC : ∀ k a as → as ⊕ k  → BarW (a ∷ as)
  barC zero a as count =
    barW-now (goodW-now (lookup! count a))
  barC (suc k) a as count  with a ∈? as
  ... | yes a∈as = barW-now (goodW-now a∈as)
  ... | no  a∉as = barW-later (λ b → barC k b (a ∷ as) (insert count a a∉as))

  barW[] : BarW []
  barW[] = barW-later (λ a → barC n a [] []⊕n)

  higmanFin : Bar []
  higmanFin = higman barW[]
