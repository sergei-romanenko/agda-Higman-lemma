-- An inductive proof of Higman's Lemma for a finite alphabet

--
-- This version tries to use relations instead of functions.
--

open import Relation.Nullary
  using (Dec; yes; no)

open import Relation.Binary.PropositionalEquality
  renaming([_] to ≡[_])

{-
module HigmanFinite
  (Letter : Set)
  (_≟_ : (a b : Letter) → Dec (a ≡ b))
  where
-}

module HigmanFinite where

postulate
  Letter : Set
  _≟_ : (a b : Letter) → Dec (a ≡ b)

open import Level
  renaming (zero to lzero; suc to lsuc)

open import Data.Bool
  using (Bool; true; false)
open import Data.Nat as Nat
  using (ℕ; zero; suc)
open import Data.Fin as Fin
open import Data.List as List
  hiding (any; all)
open import Data.List.All as All
  using (All; []; _∷_)
open import Data.List.Any as Any
  using (Any; here; there; any; index; module Membership-≡)
open import Data.Vec as Vec
  using(Vec; []; _∷_; _[_]=_; here; there; lookup; _[_]≔_; toList; fromList)
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
  now   : ∀ {ws} (n : Good ws) → Bar ws
  later : ∀ {ws} (l : ∀ w → Bar (w ∷ ws)) → Bar ws

module Illustrative-stuff where

  -- This is not used in the following, but shows how inductive bars
  -- can be used in proofs.

  -- Bar [] → ∀ ws → Bar ws

  bar[]→∀bar-w : ∀ vs → Bar vs → ∀ w → Bar (w ∷ vs)
  bar[]→∀bar-w vs (now n) w = now (good-later n)
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

  -- f // n constructs the sequence f (n - 1) , ... , f 0 .

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


--
-- prop1
--

bar[]∷ : ∀ ws → Bar([] ∷ ws)
bar[]∷ ws = later (λ w → now (good-now (⊵∃-now ([]⊴ w))))

--
-- Membership
--

open Membership-≡

infix 4 _∈?_

_∈?_ : (a : Letter) (as : List Letter) → Dec (a ∈ as)
a ∈? as = any (_≟_ a) as

--
-- GoodW & BarW
--

data GoodW : List Letter → Set where
  goodW-now   : ∀ {as a} (a∈as : a ∈ as) → GoodW (a ∷ as)
  goodW-later : ∀ {as a} (goodW-as : GoodW as) → GoodW (a ∷ as)


data BarW : List Letter → Set where
  nowW   : ∀ {as} (g : GoodW as) → BarW as
  laterW : ∀ {as} (l : ∀ a → BarW(a ∷ as)) → BarW as

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

Folder : ℕ → Set
Folder l = Vec Slot l

firsts : ∀ {l} → Folder l → Vec Letter l
firsts = Vec.map first

get-++ : Slot → Seq
get-++ s = subseq₁ s ++ subseq₂ s

seq-at : ∀ {l} i (f : Folder l) → Seq
seq-at i f = get-++ (lookup i f)

--
-- update-slot
--

update-slot : Word → Slot → Slot
update-slot u s = first s , u ∷ subseq₁ s , subseq₂ s

-- Seisenberger's `insert-folder`.

update-folder : ∀ {l} (u : Word) (i : Fin l) (f : Folder l) →
  Folder l
update-folder u i f =
  f [ i ]≔ update-slot u (lookup i f)

-- extend-folder

extend-folder : ∀ {l} (a : Letter) (u : Word) (us : Seq) (f : Folder l) →
  Folder (suc l)
extend-folder a u us f = (a , (u ∷ []) , us) ∷ f

-- _∈firsts_

infix 4 _∈firsts_

_∈firsts_ : ∀ {l} (a : Letter) (f : Folder l) → Set
a ∈firsts f = ∃ λ i →  a ≡ first (lookup i f)

--
-- Build-folder
--

data Build-folder : {l : ℕ} → Seq → Folder l → Set where
  bld-[] : Build-folder [] []
  bld-∈  : ∀ {a w ws l} (f : Folder l) (bld : Build-folder ws f)
    (a∈as : a ∈firsts f) →
    Build-folder ((a ∷ w) ∷ ws) (update-folder w (proj₁ a∈as) f)
  bld-∉ :  ∀ {a w ws l} (f : Folder l) (bld : Build-folder ws f) →
    (a∉f : ¬ a ∈firsts f) →
    Build-folder ((a ∷ w) ∷ ws) (extend-folder a w ws f)

--
-- _∈firsts?_
--

¬∈firsts[] : ∀ {a} → ¬ a ∈firsts []
¬∈firsts[] (() , _) 

¬∈firsts∷ : ∀ {l} {f : Folder l} {s} {a} →
  a ≢ first s → ¬ a ∈firsts f →
  ¬ ∃ (λ i → a ≡ first (lookup i (s ∷ f)))
¬∈firsts∷ a≢ a∉f (zero , a≡) =
  a≢ a≡
¬∈firsts∷ a≢ a∉f (suc i , a≡) =
  a∉f (i , a≡)

_∈firsts?_ : ∀ {l} (a : Letter) (f : Folder l) → Dec (a ∈firsts f)
a ∈firsts? [] = no ¬∈firsts[]
a ∈firsts? (s ∷ f) with a ≟ first s
... | yes a≡f-s = yes (zero , a≡f-s)
... | no  a≢f-s with a ∈firsts? f
... | yes (i , a≡f-i) =
  yes (suc i , a≡f-i)
... | no  a∉f =
  no (¬∈firsts∷ a≢f-s a∉f)

upd→firsts : ∀ w {l} i (f : Folder l) →
  firsts (update-folder w i f) ≡ firsts f
upd→firsts w () []
upd→firsts w zero (s ∷ f) = refl
upd→firsts w (suc i) (s ∷ f) =
  cong₂ _∷_ refl (upd→firsts w i f)

--
-- Bars
--

data Bars {l : ℕ} : Folder l → Set where
  bars-now   : ∀ {f} →
    ∀ i → Good (seq-at i f) →
    Bars f
  bars-later : ∀ {f} →
    (l : ∀ u i → Bars (update-folder u i f)) →
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
∷⊵∃ (⊵∃-now n) = ⊵∃-now (⊴-drop n)
∷⊵∃ (⊵∃-later l) = ⊵∃-later (∷⊵∃ l)

⊵∃-∷∈-++ : ∀ a w us vs →
  w ⊵∃ us ++ vs → a ∷ w ⊵∃ (a ∷∈ us) ++ vs
⊵∃-∷∈-++ a w [] vs w⊵∃vs = ∷⊵∃ w⊵∃vs
⊵∃-∷∈-++ a w (u ∷ us) vs (⊵∃-now n) = ⊵∃-now (⊴-keep n)
⊵∃-∷∈-++ a w (u ∷ us) vs (⊵∃-later a∷w⊵) =
  ⊵∃-later (⊵∃-∷∈-++ a w us vs a∷w⊵)

good-∷∈-++ : ∀ a us vs →
  Good (us ++ vs) → Good ((a ∷∈ us) ++ vs)
good-∷∈-++ a [] vs good-[]++vs =
  good-[]++vs
good-∷∈-++ a (u ∷ us) vs (good-now n) =
  good-now (⊵∃-∷∈-++ a u us vs n)
good-∷∈-++ a (u ∷ us) vs (good-later good-us++vs) =
  good-later (good-∷∈-++ a us vs good-us++vs)

-- 

∈toList∘firsts→∈firsts : ∀ {l} {f : Folder l} {a} →
  a ∈ toList (firsts f) → a ∈firsts f
∈toList∘firsts→∈firsts {zero} ()
∈toList∘firsts→∈firsts {suc l} {s ∷ f} (here refl) =
  zero , refl
∈toList∘firsts→∈firsts {suc l} {s ∷ f} (there h)
  with ∈toList∘firsts→∈firsts h
... | i , a≡ = suc i , a≡

--
-- lookup i (update-folder u j f) ≡ if i ≡ j then ... else ...
--

upd-i≡j : ∀ {l} (f : Folder l) u i →
  lookup i (update-folder u i f) ≡ update-slot u (lookup i f)
upd-i≡j [] u ()
upd-i≡j (s ∷ f) u zero = refl
upd-i≡j (s ∷ f) u (suc i) =
  upd-i≡j f u i

upd-i≢j : ∀ {l} (f : Folder l) u i j → i ≢ j →
  lookup i (update-folder u j f) ≡ lookup i f 
upd-i≢j [] u () () i≢j
upd-i≢j (s ∷ f) u zero zero 0≢0 = ⊥-elim (0≢0 refl)
upd-i≢j (s ∷ f) u zero (suc j) i≢j = refl
upd-i≢j (s ∷ f) u (suc i) zero i≢j = refl
upd-i≢j (s ∷ f) u (suc i) (suc j) suc-i≢suc-j =
  upd-i≢j f u i j (suc-i≢suc-j ∘ cong suc)

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

--
-- ∷∈-++-⋐
--

∷∈-++-⋐ : ∀ ws {l} {f : Folder l} →
  Build-folder ws f →
  (i : Fin l) →
  ∷∈-++ (lookup i f) ⋐ ws

∷∈-++-⋐ [] bld-[] ()
∷∈-++-⋐ ([] ∷ ws) () i

∷∈-++-⋐ ((a ∷ w) ∷ ws) (bld-∈ f bld (j , a≡)) i
  with i ≟Fin j
... | yes i≡j rewrite i≡j | a≡ | upd-i≡j f w j =
  update-slot→⋐ s ih
  where
  open Related.EquationalReasoning
  s = lookup j f
  ih : ∷∈-++ s ⋐ ws
  ih = ∷∈-++-⋐ ws bld j
... | no  i≢j rewrite upd-i≢j f w i j i≢j =
  is ih
  where
  open Related.EquationalReasoning
  s = lookup i f
  ih : ∷∈-++ s ⋐ ws
  ih = ∷∈-++-⋐ ws bld i
  is = ∷∈-++ s ⋐ ws ∼⟨ ⋐-drop ⟩ ∷∈-++ s ⋐ (a ∷ w) ∷ ws ∎

∷∈-++-⋐ ((a ∷ w) ∷ ws) (bld-∉ f bld a∉f) zero =
  (a ∷ w) ∷ ws ⋐ (a ∷ w) ∷ ws ∋ ⋐-refl
∷∈-++-⋐ ((a ∷ w) ∷ ws) (bld-∉ f bld a∉f) (suc i) =
  ∷∈-++ (lookup i f) ⋐ (a ∷ w) ∷ ws ∋ ⋐-drop (∷∈-++-⋐ ws bld i)

--
-- good∈folder→good
--
-- This lemma corresponds to Lemma 5.7i in Seisenberger's thesis
-- (where it is just assumed to be true "by construction").
-- However, writing out an accurate formalized proof does take
-- some effort.
--

good∈folder→good : ∀ {ws} {l} {f : Folder l} →
  Build-folder ws f →
  ∀ i → Good (seq-at i f) →
  Good ws
good∈folder→good {ws} {l} {f} bld i good-at-i =
  helper good-at-i
  where
  open Related.EquationalReasoning
  s = lookup i f
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

build-folder→¬goodW : ∀ {ws} {l} {f : Folder l} → Build-folder ws f →
  ¬ GoodW (toList (firsts f))

build-folder→¬goodW bld-[] ()
build-folder→¬goodW (bld-∈ {a} {w} f bld a∈as) goodW-f
  rewrite upd→firsts w (proj₁ a∈as) f
  = build-folder→¬goodW bld goodW-f
build-folder→¬goodW (bld-∉ f bld a∉f) (goodW-now a∈as) =
  a∉f (∈toList∘firsts→∈firsts a∈as)
build-folder→¬goodW (bld-∉ f bld a∉f) (goodW-later goodW-f) =
  build-folder→¬goodW bld goodW-f

--
-- Extending a folder with a new slot, while preserving the invariant `Bars f`.
--

mutual

  bar∷bars : ∀ {l} {f : Folder l} {a us ws} →
    Bar (us ++ ws) → Bars f →
    Bars ((a , us , ws) ∷ f)

  bar∷bars (now good-us++ws) bars-f =
    bars-now zero good-us++ws
  bar∷bars (later l-bar) bars-f =
    bar∷bars₁ l-bar bars-f

  bar∷bars₁ : ∀ {l} {f : Folder l} {a us ws} →
    (∀ w → Bar (w ∷ us ++ ws)) →
    Bars f → Bars ((a , us , ws) ∷ f)

  bar∷bars₁ l-bar (bars-now i good-at-i) =
    bars-now (suc i) good-at-i
  bar∷bars₁ {l} {f} {a} {us} {ws} l-bar (bars-later l-bars) =
    bars-later helper
    where
    helper : ∀ w i → Bars (update-folder w i ((a , us , ws) ∷ f))
    helper w zero =
      bar∷bars (l-bar w) (bars-later l-bars)
    helper w (suc i) =
      bar∷bars₁ l-bar (l-bars w i)

--
-- Now we prove a generalization of Higman's lemma
-- (which will be obtained by letting ws ≡ [] and f ≡ []).
--

mutual

  -- If `[] ∈ ws`, we get `Bar ws` immediately.
  -- Otherwise, we can turn `ws` into a folder.

  higman⊎ : ∀ ws {l} (f : Folder l) →
    Build-folder ws f → ∀ as → as ≡ toList (firsts f) →
    BarW as → Bars f → Bar ws
  higman⊎ ws f f-ws as as≡ barw-f bars-f with bar⊎all∷ ws
  ... | inj₁ bar-ws = bar-ws
  ... | inj₂ all∷ =
    higman₀ ws f all∷ f-ws as as≡ barw-f bars-f

  -- Let `as ≡ toList (firsts f)`.
  -- `as` cannot be a good letter sequence (by construction of `f`).
  -- Hence, `BarW as` implies `∀ a → BarW (a ∷ as)`.

  higman₀ : ∀ ws {l} (f : Folder l) → All∷ ws →
    Build-folder ws f → ∀ as → as ≡ toList (firsts f) →
    BarW as → Bars f → Bar ws
  higman₀ ws f all∷ f-ws as as≡ (nowW goodW-as) bars-f
    rewrite as≡
    = ⊥-elim (build-folder→¬goodW f-ws goodW-as)
  higman₀ ws f all∷ f-ws as as≡ (laterW l-f) bars-f =
    higman₁ ws f all∷ f-ws as as≡ l-f bars-f

  -- If `Bars f` contains (a representation of) a good subsequence,
  -- then ws is good. Hence, `Bar ws`.
  -- Otherwise, `∀ u i → Bars (update-folder u i f)`.

  higman₁ : ∀ ws {l} (f : Folder l) → All∷ ws →
    Build-folder ws f → ∀ as → as ≡ toList (firsts f) →
    (∀ a → BarW (a ∷ as)) → Bars f → Bar ws
  higman₁ ws f all∷ f-ws as as≡ l-f (bars-now i good-at-i) =
    now (good∈folder→good f-ws i good-at-i)
  higman₁ ws f all∷ f-ws as as≡ l-barw (bars-later l-bars) =
    later (λ w → higman₂ w ws f all∷ f-ws as as≡ l-barw l-bars)

  -- Now `∀ a → BarW (a ∷ as)`, `∀ u i → Bars (update-folder u i f))` and
  -- the word sequence *is not empty*.
  -- Hence, let's do induction on the first word of the sequence.

  higman₂ : ∀ (w : Word) ws {l} (f : Folder l) → All∷ ws →
    Build-folder ws f → ∀ as → (as≡ : as ≡ toList (firsts f)) →
    (∀ a → BarW (a ∷ as)) →
    (∀ u i → Bars (update-folder u i f)) →
    Bar (w ∷ ws)

  -- []. Bars ([] ∷ ws).
  higman₂ [] ws f all∷ f-ws as as≡ l-barw l-bars =
    bar[]∷ ws

  -- a ∷ w.
  higman₂ (a ∷ w) ws f all∷ f-ws as as≡ l-barw l-bars
    with a ∈firsts? f
  ... | yes a∈as =
    -- a ∈firsts f. f is updated to f′. So, `firsts f ≡ firsts f′`.
    Bar ws′ ∋
    higman₁ ws′ f′ ((λ ()) ∷ all∷)
            (bld-∈ f f-ws a∈as)
            as as≡f-f′
            l-barw ({- Bars f′ ∋ -} l-bars w i)
    where
      ws′ = (a ∷ w) ∷ ws
      i = proj₁ a∈as
      f′ = update-folder w i f
      open ≡-Reasoning
      as≡f-f′ = begin
        as                ≡⟨ as≡ ⟩
        toList (firsts f) ≡⟨ cong toList (sym $ upd→firsts w i f) ⟩
        toList (firsts f′) ∎
  ... | no  a∉as =
    -- a ∉firsts f. f is extended to f′. So, `a ∷ firsts f ≡ firsts f′` and
    Bar ws′ ∋
    higman₀ ws′ f′ ((λ ()) ∷ all∷)
            (bld-∉ f f-ws a∉as)
            (a ∷ as) (cong (_∷_ a) as≡)
            ({- BarW (a ∷ as) ∋ -} l-barw a) bars-f′
    where
      ws′ = (a ∷ w) ∷ ws
      f′ = extend-folder a w ws f
      bar-w∷ws : Bar (w ∷ ws)
      bar-w∷ws = higman₂ w ws f all∷ f-ws as as≡ l-barw l-bars
      bars-f′ : Bars f′
      bars-f′ = bar∷bars bar-w∷ws (bars-later l-bars)

--
-- bars[]
--

bars[] : Bars []
bars[] = bars-later helper
  where helper : ∀ u i → Bars (update-folder u i [])
        helper u ()

--
-- higman
--

higman : BarW [] → Bar []
higman barW[] = higman⊎ [] [] bld-[] [] refl barW[] bars[]
