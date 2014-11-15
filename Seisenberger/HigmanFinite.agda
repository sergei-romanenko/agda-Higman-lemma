-- An inductive proof of Higman's Lemma for a finite alphabet

--
-- This version tries to use relations instead of functions.
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

open import Data.Nat as Nat
  using (ℕ; zero; suc)
open import Data.Fin as Fin
open import Data.List as List
  hiding (any; all)
open import Data.List.All as All
  using (All; []; _∷_)
open import Data.List.Any as Any
  using (Any; here; there; any; index; module Membership; module Membership-≡)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃₂; uncurry)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using(⊥; ⊥-elim)
open import Data.Unit
  using (⊤; tt)

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
-- GoodW: a sequence of letters is "good" if there is a repeated letter.
--

data GoodW : List Letter → Set where
  goodW-now   : ∀ {as a} (a∈ : a ∈ as) → GoodW (a ∷ as)
  goodW-later : ∀ {as a} (good-as : GoodW as) → GoodW (a ∷ as)

--
-- BarW: eventually any word becomes good.
--

data BarW : List Letter → Set where
  nowW   : ∀ {as} (g : GoodW as) → BarW as
  laterW : ∀ {as} (l : ∀ a → BarW(a ∷ as)) → BarW as

-- Words and sequences

Word : Set
Word = List Letter

Seq : Set
Seq = List Word

infix 4 _⊴_ _⊵∃_

-- Homeomorphic embedding of words

data _⊴_ : Word → Word → Set where
  ⊴-[]   : [] ⊴ []
  ⊴-drop : ∀ {v w a} → v ⊴ w → v ⊴ a ∷ w
  ⊴-keep : ∀ {v w a} → v ⊴ w → a ∷ v ⊴ a ∷ w

-- [] is embeddable in any word.

[]⊴ : ∀ w → [] ⊴ w
[]⊴ [] = ⊴-[]
[]⊴ (a ∷ w) = ⊴-drop ([]⊴ w)

-- Good sequences

data _⊵∃_ (v : Word) : Seq → Set where
  ⊵∃-now   : ∀ {w ws} (n : w ⊴ v) → v ⊵∃ w ∷ ws
  ⊵∃-later : ∀ {w ws} (l : v ⊵∃ ws) → v ⊵∃ w ∷ ws

data Good : Seq → Set where
  good-now   : ∀ {ws w} (n : w ⊵∃ ws) → Good (w ∷ ws)
  good-later : ∀ {ws w} (l : Good ws) → Good (w ∷ ws)

-- Inductive bars (for sequences of words)

data Bar : Seq → Set where
  now   : ∀ {ws} (g : Good ws) → Bar ws
  later : ∀ {ws} (l : ∀ w → Bar (w ∷ ws)) → Bar ws

--
-- prop1
--

bar[]∷ : ∀ ws → Bar([] ∷ ws)
bar[]∷ ws = later (λ w → now (good-now (⊵∃-now ([]⊴ w))))

--
-- Non-empty lists
--

[]≢? : (as : Word) → Dec ([] ≢ as)
[]≢? [] = no (λ []≢[] → []≢[] refl)
[]≢? (a ∷ as) = yes (λ ())

All∷ : (ws : Seq) → Set
All∷ = All (_≢_ [])

all∷? : (ws : Seq) → Dec (All∷ ws)
all∷? ws = All.all []≢? ws

¬All∷-∷→¬All∷ : ∀ {a w ws} → ¬ All∷ ((a ∷ w) ∷ ws) → ¬ All∷ ws
¬All∷-∷→¬All∷ ¬all∷-∷ all∷ = ¬all∷-∷ ((λ ()) ∷ all∷)

--
-- Folder
--

Slot = Letter × Seq × Seq

first : Slot → Letter
first = proj₁

subseq₁ : Slot → Seq
subseq₁ = proj₁ ∘ proj₂

subseq₂ : Slot → Seq
subseq₂ = proj₂ ∘ proj₂

Folder : Set
Folder = List Slot

firsts : Folder → List Letter
firsts = map first

∈index : ∀ {f : Folder} {a} (a∈ : a ∈ firsts f) → Fin (length f)
∈index {[]} ()
∈index {s ∷ f} (here a≡) = zero
∈index {s ∷ f} (there a∈) = suc (∈index a∈)

slot-at : ∀ (f : Folder) (i : Fin (length f)) → Slot
slot-at [] ()
slot-at (s ∷ f) zero = s
slot-at (s ∷ f) (suc i) = slot-at f i

get-++ : Slot → Seq
get-++ s = subseq₁ s ++ subseq₂ s

--
-- update-slot
--

update-slot : Word → Slot → Slot
update-slot u s = first s , u ∷ subseq₁ s , subseq₂ s

-- Seisenberger's `insert-folder`.

update-folder : ∀ (u : Word) (f : Folder) (i : Fin (length f)) → Folder
update-folder u [] ()
update-folder u (s ∷ f) zero =
  update-slot u s ∷ f
update-folder u (s ∷ f) (suc i) =
  s ∷ update-folder u f i

-- extend-folder

extend-folder : ∀ (f : Folder) (a : Letter) (u : Word) (vs : Seq) → Folder
extend-folder f a u vs = (a , (u ∷ []) , vs) ∷ f

--
-- Build-folder
--

data Build-folder : Seq → Folder → Set where
  bld-[] : Build-folder [] []
  bld-∈ : ∀ {a w ws} f (bld : Build-folder ws f)
    (a∈ : a ∈ firsts f) →
    Build-folder ((a ∷ w) ∷ ws) (update-folder w f (∈index a∈))
  bld-∉ : ∀ {a w ws} f (bld : Build-folder ws f) →
    (a∉ : ¬ a ∈ firsts f) →
    Build-folder ((a ∷ w) ∷ ws) (extend-folder f a w ws)

--
-- Bars
--

data Bars : Folder → Set where
  bars-now   : ∀ {f} →
    ∀ i → Good (get-++ (slot-at f i)) →
    Bars f
  bars-later : ∀ {f} →
    (l : ∀ u i → Bars (update-folder u f i)) →
    Bars f

--
-- Subsequences
-- (As in the case of _⊴_, this is a homeomorphic embedding).
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
⊵∃-mono ⋐-[] ()
⊵∃-mono (⋐-drop vs⋐ws) v⊵∃vs =
  ⊵∃-later (⊵∃-mono vs⋐ws v⊵∃vs)
⊵∃-mono (⋐-keep vs⋐ws) (⊵∃-now v′⊴v) =
  ⊵∃-now v′⊴v
⊵∃-mono (⋐-keep vs⋐ws) (⊵∃-later v⊵∃vs) =
  ⊵∃-later (⊵∃-mono vs⋐ws v⊵∃vs)

good-mono : ∀ {vs ws} → vs ⋐ ws → Good vs → Good ws
good-mono ⋐-[] ()
good-mono (⋐-drop vs⋐ws) good-vs =
  good-later (good-mono vs⋐ws good-vs)
good-mono (⋐-keep vs⋐ws) (good-now v⊵∃vs) =
  good-now (⊵∃-mono vs⋐ws v⊵∃vs)
good-mono (⋐-keep vs⋐ws) (good-later good-vs) =
  good-later (good-mono vs⋐ws good-vs)

--
-- "Division" of sequences
--   (a ∷∈ us) ++ vs ≡ ws
--
-- The following function adds a letter to each word in a word list.
-- (In a sense, this is "multiplication".)

infixr 5 _∷∈_

_∷∈_ : (a : Letter) (ws : List Word) → List Word
a ∷∈ [] = []
a ∷∈ (w ∷ ws) = (a ∷ w) ∷ a ∷∈ ws

∷∈-++ : Slot → Seq
∷∈-++ s = (first s ∷∈ subseq₁ s) ++ subseq₂ s

--
-- Good (us ++ vs) → Good ((a ∷∈ us) ++ vs)
--

∷⊵∃ : ∀ {a w ws} → w ⊵∃ ws → a ∷ w ⊵∃ ws
∷⊵∃ (⊵∃-now g) = ⊵∃-now (⊴-drop g)
∷⊵∃ (⊵∃-later l) = ⊵∃-later (∷⊵∃ l)

⊵∃-∷∈-++ : ∀ a w us vs →
  w ⊵∃ us ++ vs → a ∷ w ⊵∃ (a ∷∈ us) ++ vs
⊵∃-∷∈-++ a w [] vs w⊵∃vs = ∷⊵∃ w⊵∃vs
⊵∃-∷∈-++ a w (u ∷ us) vs (⊵∃-now g) = ⊵∃-now (⊴-keep g)
⊵∃-∷∈-++ a w (u ∷ us) vs (⊵∃-later a∷w⊵) =
  ⊵∃-later (⊵∃-∷∈-++ a w us vs a∷w⊵)

good-∷∈-++ : ∀ a us vs →
  Good (us ++ vs) → Good ((a ∷∈ us) ++ vs)
good-∷∈-++ a [] vs good-[]++vs =
  good-[]++vs
good-∷∈-++ a (u ∷ us) vs (good-now g) =
  good-now (⊵∃-∷∈-++ a u us vs g)
good-∷∈-++ a (u ∷ us) vs (good-later good-us++vs) =
  good-later (good-∷∈-++ a us vs good-us++vs)

-- firsts (update-folder w i f) ≡ firsts f

upd→firsts : ∀ w f i →
  firsts (update-folder w f i) ≡ firsts f
upd→firsts w [] ()
upd→firsts w (s ∷ f) zero = refl
upd→firsts w (s ∷ f) (suc i) =
  cong₂ _∷_ refl (upd→firsts w f i)

--
-- _≡_ is decidable for Fin n.
-- (For some reason, this is not in the standard library...)
--

fin-suc-injective : ∀ {l} {m n : Fin l} → Fin.suc m ≡ Fin.suc n → m ≡ n
fin-suc-injective refl = refl


infix 4 _≟Fin_

_≟Fin_ : ∀ {l} (m n : Fin l) → Dec (m ≡ n)
zero ≟Fin zero = yes refl
zero ≟Fin suc n = no (λ ())
suc m ≟Fin zero = no (λ ())
suc m ≟Fin suc n with m ≟Fin n
... | yes m≡n = yes (cong suc m≡n)
... | no  m≢n = no (λ sm≡sn → m≢n (fin-suc-injective sm≡sn))

-- index↓

index↓ : ∀ u f (i : Fin (length f)) (j : Fin (length (update-folder u f i))) →
           Fin (length f)
index↓ u [] () j
index↓ u (s ∷ f) zero j = j
index↓ u (s ∷ f) (suc i) zero = zero
index↓ u (s ∷ f) (suc i) (suc j) =
  suc (index↓ u f i j)

--
-- slot-at (update-folder f u i) j ≡ if i ≡ j then ... else ...
--

upd-≡ : ∀ u f i j → i ≡ index↓ u f i j →
  slot-at (update-folder u f i) j ≡ update-slot u (slot-at f i)
upd-≡ u [] () j i≡j
upd-≡ u (s ∷ f) zero .zero refl = refl
upd-≡ u (s ∷ f) (suc i) zero ()
upd-≡ u (s ∷ f) (suc i) (suc j) si≡sj =
  upd-≡ u f i j (fin-suc-injective si≡sj)

upd-≢ : ∀ u f i j → i ≢ index↓ u f i j →
  slot-at (update-folder u f i) j ≡ slot-at f (index↓ u f i j)
upd-≢ u [] () j i≢j
upd-≢ u (s ∷ f) zero zero 0≢0 = ⊥-elim (0≢0 refl)
upd-≢ u (s ∷ f) zero (suc j) i≢j = refl
upd-≢ u (s ∷ f) (suc i) zero i≢j = refl
upd-≢ u (s ∷ f) (suc i) (suc j) si≢sj =
  upd-≢ u f i j (si≢sj ∘ cong suc)

--
-- Build-folder ws f → (a , us , vs) ∈ f → (a ∷∈ us) ++ vs ⋐ ws
--

-- update-slot→⋐

update-slot→⋐ : ∀ {w ws} s →
  ∷∈-++ s ⋐ ws →
    ∷∈-++ (update-slot w s) ⋐ (first s ∷ w) ∷ ws
update-slot→⋐ {w} {ws} s =
  ∷∈-++ s ⋐ ws
    ≡⟨ refl ⟩
  (a ∷∈ us) ++ vs ⋐ ws
    ∼⟨ ⋐-keep ⟩
  (a ∷ w) ∷ (a ∷∈ us) ++ vs ⋐ (a ∷ w) ∷ ws
    ≡⟨ refl ⟩
  ((a ∷∈ w ∷ us) ++ vs) ⋐ (a ∷ w) ∷ ws
    ≡⟨ refl ⟩
  ∷∈-++ (a , w ∷ us , vs) ⋐ (a ∷ w) ∷ ws
    ≡⟨ refl ⟩
  ∷∈-++ (update-slot w s) ⋐ (first s ∷ w) ∷ ws
  ∎
  where
  open Related.EquationalReasoning
  a = first s; us = subseq₁ s; vs = subseq₂ s


-- (a∈ : a ∈ firsts f) → a ≡ first (slot-at f (∈index a∈))

a∈→a≡ : ∀ f {a} (a∈ : a ∈ firsts f)
          {i} (i≡ : i ≡ ∈index a∈) → a ≡ first (slot-at f i)
a∈→a≡ [] () i≡
a∈→a≡ (s ∷ f) (here a≡) refl = a≡
a∈→a≡ (s ∷ f) (there a∈) {zero} ()
a∈→a≡ (s ∷ f) (there a∈) {suc i} si≡ =
  a∈→a≡ f a∈ (fin-suc-injective si≡)

--
-- ∷∈-++-⋐
--

∷∈-++-⋐ : ∀ ws {f} →
  Build-folder ws f →
  ∀ (j : Fin (length f)) →
  ∷∈-++ (slot-at f j) ⋐ ws

∷∈-++-⋐ [] bld-[] ()
∷∈-++-⋐ ([] ∷ ws) () i

∷∈-++-⋐ ((a ∷ w) ∷ ws) (bld-∈ {.a} f bld a∈) j
  with ∈index a∈ | inspect ∈index a∈
... | i | ≡[ ≡i ] with i ≟Fin (index↓ w f i j)
... | yes i≡j rewrite upd-≡ w f i j i≡j | a∈→a≡ f a∈ (sym $ ≡i)
  = update-slot→⋐ s ih
  where
  s = slot-at f i
  ih : ∷∈-++ s ⋐ ws
  ih = ∷∈-++-⋐ ws bld i
... | no  i≢j rewrite upd-≢ w f i j i≢j
  = is ih
  where
  open Related.EquationalReasoning
  j↓ = index↓ w f i j
  s = slot-at f j↓
  ih : ∷∈-++ s ⋐ ws
  ih = ∷∈-++-⋐ ws bld j↓
  is = ∷∈-++ s ⋐ ws ∼⟨ ⋐-drop ⟩ ∷∈-++ s ⋐ (a ∷ w) ∷ ws ∎

∷∈-++-⋐ ((a ∷ w) ∷ ws) (bld-∉ f bld a∉) zero =
  (a ∷ w) ∷ ws ⋐ (a ∷ w) ∷ ws ∋ ⋐-refl
∷∈-++-⋐ ((a ∷ w) ∷ ws) (bld-∉ f bld a∉) (suc i) =
  ∷∈-++ (slot-at f i) ⋐ (a ∷ w) ∷ ws ∋ ⋐-drop (∷∈-++-⋐ ws bld i)

--
-- good∈folder→good
--
-- This lemma corresponds to Lemma 5.7i in Seisenberger's thesis
-- (where it is just assumed to be true "by construction").
-- However, writing out an accurate formalized proof does take
-- some effort.
--

good∈folder→good : ∀ {ws f} →
  Build-folder ws f →
  ∀ i → Good (get-++ (slot-at f i)) →
  Good ws
good∈folder→good {ws} {f} bld i good-at-i =
  helper good-at-i
  where
  open Related.EquationalReasoning
  s = slot-at f i
  a = first s; us = subseq₁ s; vs = subseq₂ s

  [a∷∈us]++vs⋐ws : (a ∷∈ us) ++ vs ⋐ ws
  [a∷∈us]++vs⋐ws = ∷∈-++-⋐ ws bld i
  
  helper =
    Good (us ++ vs)
      ∼⟨ good-∷∈-++ a us vs ⟩
    Good ((a ∷∈ us) ++ vs)
      ∼⟨ good-mono [a∷∈us]++vs⋐ws ⟩
    Good ws
    ∎

--
-- ∀ ws → Bar ws ⊎ All∷ ws
--   If [] ∈ ws, then [] ⊴ w for any subsequent word w,
--   otherwise, all w ∈ ws are not empty.
--

-- bar→bar∷

bar→bar∷ : ∀ {w ws} → Bar ws → Bar (w ∷ ws)
bar→bar∷ (now g) = now (good-later g)
bar→bar∷ {w} (later l) = l w

-- ¬all∷→bar

¬all∷→bar : ∀ ws → ¬ All∷ ws → Bar ws
¬all∷→bar [] ¬all∷ = ⊥-elim (¬all∷ [])
¬all∷→bar ([] ∷ ws) ¬all∷ = bar[]∷ ws
¬all∷→bar ((a ∷ w) ∷ ws) ¬all∷ =
  bar→bar∷ (¬all∷→bar ws (λ z → ¬all∷ ((λ ()) ∷ z)))

-- bar⊎all∷

bar⊎all∷ : ∀ ws → Bar ws ⊎ All∷ ws
bar⊎all∷ ws with all∷? ws
... | yes all∷ = inj₂ all∷
... | no ¬all∷ = inj₁ (¬all∷→bar ws ¬all∷)

--
-- build-folder→¬goodW
--

build-folder→¬goodW : ∀ {ws f} → Build-folder ws f →
  ¬ GoodW (firsts f)
build-folder→¬goodW bld-[] ()
build-folder→¬goodW (bld-∈ {a} {w} f bld a∈) goodW-f
  rewrite upd→firsts w f (∈index a∈)
  = build-folder→¬goodW bld goodW-f
build-folder→¬goodW (bld-∉ f bld a∉) (goodW-now a∈) =
  ⊥-elim (a∉ a∈)
build-folder→¬goodW (bld-∉ f bld a∉) (goodW-later goodW-f) =
  build-folder→¬goodW bld goodW-f

--
-- Extending a folder with a new slot, while preserving the invariant `Bars f`.
--

mutual

  extend-bars : ∀ {s f} →
    Bar (get-++ s) → Bars f →
    Bars (s ∷ f)

  extend-bars (now good-++) bars-f =
    bars-now zero good-++
  extend-bars (later l-bar) bars-f =
    extend-bars₁ l-bar bars-f

  extend-bars₁ : ∀ {s f} →
    (∀ w → Bar (w ∷ get-++ s)) → Bars f →
    Bars (s ∷ f)
  extend-bars₁ l-bar (bars-now i good-at-i) =
    bars-now (suc i) good-at-i
  extend-bars₁ {s} {f} l-bar (bars-later l-bars) =
    bars-later helper
    where helper : ∀ u i → Bars (update-folder u (s ∷ f) i)
          helper u zero =
            extend-bars (l-bar u) (bars-later l-bars)
          helper u (suc i) =
            extend-bars₁ l-bar (l-bars u i)

--
-- Now we prove a generalization of Higman's lemma
-- (which will be obtained by letting ws ≡ [] and f ≡ []).
--

mutual

  -- If `[] ∈ ws`, we get `Bar ws` immediately.
  -- Otherwise, we can turn `ws` into a folder.

  higman⊎ : ∀ ws f →
    Build-folder ws f → ∀ as → as ≡ firsts f →
    BarW as → Bars f → Bar ws
  higman⊎ ws f bld as as≡ barw-f bars-f with bar⊎all∷ ws
  ... | inj₁ bar-ws = bar-ws
  ... | inj₂ all∷ =
    higman₀ ws f all∷ bld as as≡ barw-f bars-f

  -- Let `as ≡ firsts f`.
  -- `as` cannot be a good letter sequence (by construction of `f`).
  -- Hence, `BarW as` implies `∀ a → BarW (a ∷ as)`.

  higman₀ : ∀ ws f → All∷ ws →
    Build-folder ws f → ∀ as → as ≡ firsts f →
    BarW as → Bars f → Bar ws
  higman₀ ws f all∷ bld as as≡ (nowW good-as) bars-f
    rewrite as≡
    = ⊥-elim (build-folder→¬goodW bld good-as)
  higman₀ ws f all∷ bld as as≡ (laterW l-barw) bars-f =
    higman₁ ws f all∷ bld as as≡ l-barw bars-f

  -- If `Bars f` contains (a representation of) a good subsequence,
  -- then ws is good. Hence, `Bar ws`.
  -- Otherwise, `∀ u i → Bars (update-folder u i f)`.

  higman₁ : ∀ ws f → All∷ ws →
    Build-folder ws f → ∀ as → as ≡ firsts f →
    (∀ a → BarW (a ∷ as)) → Bars f → Bar ws
  higman₁ ws f all∷ bld as as≡ l-barw (bars-now a∈ good-at-i) =
    now (good∈folder→good bld a∈ good-at-i)
  higman₁ ws f all∷ bld as as≡ l-barw (bars-later l-bars) =
    later (λ w → higman₂ w ws f all∷ bld as as≡ l-barw l-bars)

  -- Now `∀ a → BarW (a ∷ as)`, `∀ u i → Bars (update-folder u i f))` and
  -- the word sequence *is not empty*.
  -- Hence, let's do induction on the first word of the sequence.

  higman₂ : ∀ (w : Word) ws f → All∷ ws →
    Build-folder ws f → ∀ as → as ≡ firsts f →
    (∀ a → BarW (a ∷ as)) →
    (∀ u i → Bars (update-folder u f i)) →
    Bar (w ∷ ws)

  -- []. Bars ([] ∷ ws).
  higman₂ [] ws f all∷ bld as as≡ l-barw l-bars =
    bar[]∷ ws

  -- a ∷ w.
  higman₂ (a ∷ w) ws f all∷ bld as as≡ l-barw l-bars
    with a ∈? firsts f
  ... | yes a∈as =
    -- a ∈firsts f. f is updated to f′. So, `firsts f ≡ firsts f′`.
    Bar ws′ ∋
    higman₁ ws′ f′ ((λ ()) ∷ all∷)
            (bld-∈ f bld a∈as)
            as as≡as′
            l-barw (l-bars w (∈index a∈as))
    where
      ws′ = (a ∷ w) ∷ ws
      f′ = update-folder w f (∈index a∈as)
      open ≡-Reasoning
      as≡as′ = begin
        as ≡⟨ as≡ ⟩ firsts f ≡⟨ sym $ upd→firsts w f (∈index  a∈as) ⟩ firsts f′ ∎
  ... | no  a∉as =
    -- a ∉firsts f. f is extended to f′. So, `a ∷ firsts f ≡ firsts f′` and
    Bar ws′ ∋
    higman₀ ws′ f′ ((λ ()) ∷ all∷)
            (bld-∉ f bld a∉as)
            (a ∷ as) (cong (_∷_ a) as≡)
            (l-barw a) bars-f′
    where
      ws′ = (a ∷ w) ∷ ws
      f′ = extend-folder f a w ws
      bar-w∷ws : Bar (w ∷ ws)
      bar-w∷ws = higman₂ w ws f all∷ bld as as≡ l-barw l-bars
      bars-f′ : Bars f′
      bars-f′ = extend-bars bar-w∷ws (bars-later l-bars)

--
-- bars[]
--

bars[] : Bars []
bars[] = bars-later helper
  where helper : ∀ u i → Bars (update-folder u [] i)
        helper u ()

--
-- higman
--

higman : BarW [] → Bar []
higman barW[] = higman⊎ [] [] bld-[] [] refl barW[] bars[]
