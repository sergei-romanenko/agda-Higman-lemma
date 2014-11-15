module HigmanFiniteExamples where

open import Data.Nat as Nat
  using (ℕ; zero; suc)
open import Data.List as List
  hiding (any; all)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃₂; uncurry)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using(⊥; ⊥-elim)

open import Function
import Function.Related as Related

open import Relation.Nullary
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

