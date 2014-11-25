--
-- An inductive proof of Higman's Lemma for a finite alphabet
--

open import Relation.Nullary
  using (Dec; yes; no)

open import Relation.Binary.PropositionalEquality as P
  renaming([_] to ≡[_])

module HigmanFinite
  (Letter : Set)
  (_≟_ : (a b : Letter) → Dec (a ≡ b))
  where

{-
module HigmanFinite where

postulate
  Letter : Set
  _≟_ : (a b : Letter) → Dec (a ≡ b)
-}

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Data.List as List
  hiding (any; all)
open import Data.List.All as All
  using (All; []; _∷_)
open import Data.List.Any as Any
  using (Any; here; there; any; module Membership; module Membership-≡)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using(⊥; ⊥-elim)

open import Function
import Function.Related as Related

open import Relation.Nullary

--
-- Membership
--

open Membership-≡

infix 4 _∈?_

_∈?_ : (a : Letter) (as : List Letter) → Dec (a ∈ as)
a ∈? as = any (_≟_ a) as

--
-- `GoodW as`: `as` is "good" if there is a repeated letter.
--  Namely, as ≡ ... ∷ a′′ ∷ ... ∷ a′ ∷ ... ∷ [] and a′ ≡ a′′ .
--

data GoodW : List Letter → Set where
  goodW-now   : ∀ {as a} (a∈ : a ∈ as) → GoodW (a ∷ as)
  goodW-later : ∀ {as a} (good-as : GoodW as) → GoodW (a ∷ as)

--
-- `BarW as`: eventually any continuation of `as` becomes good.
--

data BarW : List Letter → Set where
  barW-now   : ∀ {as} (g : GoodW as) → BarW as
  barW-later : ∀ {as} (l : ∀ a → BarW(a ∷ as)) → BarW as

-- Words and sequences.

Word : Set
Word = List Letter

Seq : Set
Seq = List Word

infix 4 _⊵_ _⊵∃_

-- Homeomorphic embedding of words.

data _⊵_ : Word → Word → Set where
  ⊵-[]   : [] ⊵ []
  ⊵-drop : ∀ {w v a} → w ⊵ v → a ∷ w ⊵ v
  ⊵-keep : ∀ {w v a} → w ⊵ v → a ∷ w ⊵ a ∷ v

-- [] is embeddable in any word.

⊵[] : ∀ w → w ⊵ []
⊵[] [] = ⊵-[]
⊵[] (a ∷ w) = ⊵-drop (⊵[] w)

--
-- `Good ws`: `ws` is "good" if
--  ws ≡ ... ∷ w′′ ∷ ... ∷ w′ ∷ ... ∷ [] and w′′ ⊵ w′ .
--

_⊵∃_ : (w : Word) (ws : Seq) → Set
w ⊵∃ ws = Any (_⊵_ w) ws

data Good : Seq → Set where
  good-now   : ∀ {ws w} (n : w ⊵∃ ws) → Good (w ∷ ws)
  good-later : ∀ {ws w} (l : Good ws) → Good (w ∷ ws)

--
-- Inductive bars (for sequences of words)
-- `Bar ws`: eventually any continuation of `ws` becomes good.
--

data Bar : Seq → Set where
  now   : ∀ {ws} (g : Good ws) → Bar ws
  later : ∀ {ws} (l : ∀ w → Bar (w ∷ ws)) → Bar ws

--
-- In some papers this lemma is called "prop1".
-- (A very expressiove and informative name...) :-)
--

bar[]∷ : ∀ ws → Bar([] ∷ ws)
bar[]∷ ws = later (λ w → now (good-now (here (⊵[] w))))

--
-- Folder
--

Slot = Letter × Seq × Seq

label : Slot → Letter
label = proj₁

seq₁ : Slot → Seq
seq₁ = proj₁ ∘ proj₂

seq₂ : Slot → Seq
seq₂ = proj₂ ∘ proj₂

Folder : Set
Folder = List Slot

labels : Folder → List Letter
labels = map label

seq₁++seq₂ : Slot → Seq
seq₁++seq₂ s = seq₁ s ++ seq₂ s

--
-- Updating folders.
-- (This corresponds to Seisenberger's `insert-folder`.)
--

update : ∀ f (u : Word) {a} (a∈ : a ∈ labels f) → Folder
update [] u ()
update (s ∷ f) u (here a≡) =
  (label s , u ∷ seq₁ s , seq₂ s) ∷ f
update (s ∷ f) u (there a∈) =
  s ∷ update f u a∈

-- Extending  folders.

extend : ∀ (f : Folder) (a : Letter) (u : Word) (vs : Seq) → Folder
extend f a u vs = (a , (u ∷ []) , vs) ∷ f

--
-- Building a folder from a word sequence.
-- (Here Seisenberger defines a function, but we use a relation.)
--

data Build : Seq → Folder → Set where
  bld-[] : Build [] []
  bld-∈ : ∀ {a w ws} f (bld : Build ws f)
    (a∈ : a ∈ labels f) →
    Build ((a ∷ w) ∷ ws) (update f w a∈)
  bld-∉ : ∀ {a w ws} f (bld : Build ws f) →
    (a∉ : ¬ a ∈ labels f) →
    Build ((a ∷ w) ∷ ws) (extend f a w ws)

--
-- Bars
--

data Bars : Folder → Set where
  bars-now   : ∀ {f s} →
    s ∈ f → Good (seq₁++seq₂ s) →
    Bars f
  bars-later : ∀ {f} →
    (l : ∀ u {a} (a∈ : a ∈ labels f) → Bars (update f u a∈)) →
    Bars f

--
-- Subsequences
-- (As in the case of _⊵_, this is a homeomorphic embedding).
--

infix 4 _⋐_

data _⋐_ : Seq → Seq → Set where
  ⋐-[]   : [] ⋐ []
  ⋐-drop : ∀ {vs ws v} → vs ⋐ ws → vs ⋐ v ∷ ws
  ⋐-keep : ∀ {vs ws v} → vs ⋐ ws → v ∷ vs ⋐ v ∷ ws

⋐-refl : ∀ {ws} → ws ⋐ ws
⋐-refl {[]} = ⋐-[]
⋐-refl {w ∷ ws} = ⋐-keep (⋐-refl {ws})

-- The monotonicity of _⊵∃_ and Good with respect to _⋐_ .

⊵∃-mono : ∀ {v vs ws} → vs ⋐ ws → v ⊵∃ vs → v ⊵∃ ws
⊵∃-mono ⋐-[] v⊵∃ = v⊵∃
⊵∃-mono (⋐-drop vs⋐) v⊵∃ =
  there (⊵∃-mono vs⋐ v⊵∃)
⊵∃-mono (⋐-keep vs⋐) (here v⊵) =
  here v⊵
⊵∃-mono (⋐-keep vs⋐) (there v⊵∃) =
  there (⊵∃-mono vs⋐ v⊵∃)

good-mono : ∀ {vs ws} → vs ⋐ ws → Good vs → Good ws
good-mono ⋐-[] ()
good-mono (⋐-drop vs⋐) good-vs =
  good-later (good-mono vs⋐ good-vs)
good-mono (⋐-keep vs⋐) (good-now v⊵∃) =
  good-now (⊵∃-mono vs⋐ v⊵∃)
good-mono (⋐-keep vs⋐) (good-later good-vs) =
  good-later (good-mono vs⋐ good-vs)

--
-- The following function adds a letter to each word in a word list.
-- 

infixr 6 _∷∈_

_∷∈_ : (a : Letter) (ws : List Word) → List Word
a ∷∈ ws = map (_∷_ a) ws

-- "Zipping" a slot, to restore a subsequence of the original sequence.
-- ∷∈-++ (a , us , vs) ≡ (a ∷∈ us) ++ vs

∷∈-++ : Slot → Seq
∷∈-++ s = (label s ∷∈ seq₁ s) ++ seq₂ s

--
-- Good (us ++ vs) → Good ((a ∷∈ us) ++ vs)
--

∷⊵∃ : ∀ {a w ws} → w ⊵∃ ws → a ∷ w ⊵∃ ws
∷⊵∃ (here w⊵) = here (⊵-drop w⊵)
∷⊵∃ (there w⊵∃) = there (∷⊵∃ w⊵∃)

⊵∃-∷∈-++ : ∀ {a w} us {vs} →
  w ⊵∃ us ++ vs → a ∷ w ⊵∃ (a ∷∈ us) ++ vs
⊵∃-∷∈-++ [] w⊵∃ = ∷⊵∃ w⊵∃
⊵∃-∷∈-++ (u ∷ us) (here w⊵) =
  here (⊵-keep w⊵)
⊵∃-∷∈-++ (u ∷ us) (there w⊵∃) =
  there (⊵∃-∷∈-++ us w⊵∃)

good-∷∈-++ : ∀ a us vs →
  Good (us ++ vs) → Good ((a ∷∈ us) ++ vs)
good-∷∈-++ a [] vs good-[]++vs =
  good-[]++vs
good-∷∈-++ a (u ∷ us) vs (good-now g) =
  good-now (⊵∃-∷∈-++ us g)
good-∷∈-++ a (u ∷ us) vs (good-later good-us++vs) =
  good-later (good-∷∈-++ a us vs good-us++vs)

--
-- Now we are going to prove a subtle fact:
-- if there is a slot `(a , us , vs)` such that `Good (us ++ vs)`,
-- then `Good ws`.
--

⋐-upd : ∀ {f ws a u} →
  (a∈ : a ∈ labels f) →
  (∀ {s} → s ∈ f → ∷∈-++ s ⋐ ws) →
  (∀ {s} → s ∈ update f u a∈ → (∷∈-++ s) ⋐ ((a ∷ u) ∷ ws))

⋐-upd {[]} () hf s∈
⋐-upd {s ∷ f} (here refl) hf (here refl) =
  ⋐-keep (hf (here refl))
⋐-upd {s ∷ f} (here refl) hf (there s∈) =
  ⋐-drop (hf (there s∈))
⋐-upd {s ∷ f} (there a∈) hf (here refl) =
  ⋐-drop (hf (here refl))
⋐-upd {s ∷ f} (there a∈) hf (there s∈) =
  ⋐-upd a∈ (λ s′∈f → hf (there s′∈f)) s∈

--
-- ∷∈-++-⋐
--

∷∈-++-⋐ : ∀ {ws f} →
  Build ws f →
  ∀ {s} → s ∈ f → ∷∈-++ s ⋐ ws

∷∈-++-⋐ bld-[] ()
∷∈-++-⋐ (bld-∈ f bld a∈) {s} s∈f =
  ⋐-upd a∈ (∷∈-++-⋐ bld) s∈f
∷∈-++-⋐ (bld-∉ f bld a∉) (here refl) =
  ⋐-refl
∷∈-++-⋐ (bld-∉ f bld a∉) {s} (there s∈f) =
  ⋐-drop (∷∈-++-⋐ bld s∈f)

--
-- good∈folder→good
--
-- This lemma corresponds to Lemma 5.7i in Seisenberger's thesis
-- (where it is just assumed to be true "by construction").
-- However, writing out an accurate formalized proof does take
-- some effort.
--

good∈folder→good : ∀ {ws f} →
  Build ws f →
  ∀ {s} → s ∈ f → Good (seq₁++seq₂ s) →
  Good ws
good∈folder→good {ws} {f} bld {s} s∈f good-s =
  helper good-s
  where
  open Related.EquationalReasoning
  a = label s; us = seq₁ s; vs = seq₂ s

  [a∷∈us]++vs⋐ws : (a ∷∈ us) ++ vs ⋐ ws
  [a∷∈us]++vs⋐ws = ∷∈-++-⋐ bld s∈f
  
  helper =
    Good (us ++ vs)
      ∼⟨ good-∷∈-++ a us vs ⟩
    Good ((a ∷∈ us) ++ vs)
      ∼⟨ good-mono [a∷∈us]++vs⋐ws ⟩
    Good ws
    ∎

--
-- labels (update f u {a} a∈) ≡ labels f
--

labels∘update≡ : ∀ f u {a} a∈ →
  labels (update f u {a} a∈) ≡ labels f
labels∘update≡ [] u ()
labels∘update≡ (s ∷ f) u (here refl) =
  refl
labels∘update≡ (s ∷ f) u (there a∈) =
  cong₂ _∷_ refl (labels∘update≡ f u a∈)

--
-- Build ws f → ¬ GoodW (labels f)
--

bld→¬goodW : ∀ {ws f} →
  Build ws f → ¬ GoodW (labels f)
bld→¬goodW bld-[] ()
bld→¬goodW (bld-∈ {a} {w} f bld a∈) goodW-f
  rewrite labels∘update≡ f w a∈
  = bld→¬goodW bld goodW-f
bld→¬goodW (bld-∉ f bld a∉) (goodW-now a∈) =
  ⊥-elim (a∉ a∈)
bld→¬goodW (bld-∉ f bld a∉) (goodW-later goodW-f) =
  bld→¬goodW bld goodW-f

--
-- Extending a folder with a new slot, while preserving the invariant `Bars f`.
--

mutual

  extend-bars : ∀ {s f} →
    Bar (seq₁++seq₂ s) → Bars f →
    Bars (s ∷ f)

  extend-bars (now good-++) bars-f =
    bars-now (here refl) good-++
  extend-bars (later l-bar) bars-f =
    extend-bars₁ l-bar bars-f

  extend-bars₁ : ∀ {s f} →
    (∀ w → Bar (w ∷ seq₁++seq₂ s)) → Bars f →
    Bars (s ∷ f)
  extend-bars₁ l-bar (bars-now s∈f good-s) =
    bars-now (there s∈f) good-s
  extend-bars₁ {s} {f} l-bar (bars-later l-bars) =
    bars-later (extend-bars₂ l-bar l-bars)
  extend-bars₂ : ∀ {s f} →
    (∀ w → Bar (w ∷ seq₁++seq₂ s)) →
    (∀ u {a} a∈ → Bars (update f u a∈)) →
    (∀ u {a} a∈ → Bars (update (s ∷ f) u a∈))
  extend-bars₂ l-bar l-bars u (here a≡) =
    extend-bars (l-bar u) (bars-later l-bars)
  extend-bars₂ l-bar l-bars u (there a∈) =
    extend-bars₁ l-bar (l-bars u a∈)

--
-- Now we prove a generalization of Higman's lemma
-- (which will be obtained by letting ws ≡ [] and f ≡ []).
--

mutual

  -- Let `as ≡ labels f`.
  -- `as` cannot be a good letter sequence (by construction of `f`).
  -- Hence, `BarW as` implies `∀ a → BarW (a ∷ as)`.

  higman₀ : ∀ ws f →
    Build ws f → ∀ {as} → as ≡ labels f →
    BarW as → Bars f →
    Bar ws
  higman₀ ws f bld as≡ (barW-now good-as) bars-f
    rewrite as≡
    = ⊥-elim (bld→¬goodW bld good-as)
  higman₀ ws f bld as≡ (barW-later l-barw) bars-f =
    higman₁ ws f bld as≡ l-barw bars-f

  -- If `Bars f` contains (a representation of) a good subsequence,
  -- then ws is good. Hence, `Bar ws`.
  -- Otherwise, `∀ u {a} a∈ → Bars (update f u a∈)`.

  higman₁ : ∀ ws f →
    Build ws f → ∀ {as} → as ≡ labels f →
    (∀ a → BarW (a ∷ as)) → Bars f →
    Bar ws
  higman₁ ws f bld as≡ l-barw (bars-now s∈f good-s) =
    now (good∈folder→good bld s∈f good-s)
  higman₁ ws f bld as≡ l-barw (bars-later l-bars) =
    later (λ w → higman₂ w ws f bld as≡ l-barw l-bars)

  -- Now `∀ a → BarW (a ∷ as)`, `∀ u {a} a∈ → Bars (update f u a∈)` and
  -- the word sequence *is not empty*.
  -- Hence, let's do induction on the first word of the sequence.

  higman₂ : ∀ w ws f →
    Build ws f → ∀ {as} → as ≡ labels f →
    (∀ a → BarW (a ∷ as)) → (∀ u {a} a∈ → Bars (update f u a∈)) →
    Bar (w ∷ ws)

  -- []. Bar ([] ∷ ws).
  higman₂ [] ws f bld as≡ l-barw l-bars =
    bar[]∷ ws

  -- a ∷ w.
  higman₂ (a ∷ w) ws f bld as≡ l-barw l-bars
    with a ∈? labels f
  ... | yes a∈as =
    -- a ∈labels f. f is updated to f′. So, `labels f ≡ labels f′`.
    higman₁ ((a ∷ w) ∷ ws) (update f w a∈as)
            (bld-∈ f bld a∈as)
            (trans as≡ (sym $ labels∘update≡ f w a∈as))
            l-barw (l-bars w a∈as)
  ... | no  a∉as =
    -- a ∉labels f. f is extended to f′. So, `a ∷ labels f ≡ labels f′`.
    higman₀ ((a ∷ w) ∷ ws) (extend f a w ws)
            (bld-∉ f bld a∉as)
            (cong (_∷_ a) as≡)
            (l-barw a)
            (extend-bars {a , w ∷ [] , ws} {f}
                         (Bar (w ∷ ws) ∋ higman₂ w ws f bld as≡ l-barw l-bars)
                         (Bars f ∋ bars-later l-bars))

--
-- bars[]
--

bars[] : Bars []
bars[] = bars-later (λ u {a} → λ ())

--
-- higman
--

higman : BarW [] → Bar []
higman barW[] = higman₀ [] [] bld-[] refl barW[] bars[]
