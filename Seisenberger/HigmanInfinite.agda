
open import Level
  renaming (zero to lzero; suc to lsuc)
open import Relation.Binary
  using (Rel; Decidable; Transitive)
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

{-
module HigmanInfinite
  (A : Set)
  (_≥_ : Rel A lzero)
  (≥-trans : Transitive _≥_)
  (_≥?_ : Decidable {A = A} _≥_)
  where
-}

module HigmanInfinite where

postulate
  A : Set
  _≥_ : Rel A lzero
  ≥-trans : Transitive _≥_
  _≥?_ : Decidable {A = A} _≥_


open import Data.List as List
  hiding (any; all; tails)
open import Data.List.All as All
  using (All; []; _∷_)
open import Data.List.Any as Any
  using (Any; here; there; any; index; module Membership-≡)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using(⊥; ⊥-elim)

open import Relation.Nullary
  using (Dec; yes; no; ¬_)

open import Function
import Function.Related as Related

--
-- Words
--

Word = List A
Seq = List Word

_≥∃_ : (a : A) (as : List A) → Set
a ≥∃ as = Any (_≥_ a) as

_≥∃?_ : (a : A) (as : List A) → Dec (a ≥∃ as)
a ≥∃? as = any (_≥?_ a) as

--
-- `GoodW as`: `as` is "good" if there is a repeated letter.
--  Namely, as ≡ ... ∷ a′′ ∷ ... ∷ a′ ∷ ... ∷ [] and a′ ≡ a′′ .
--

data GoodW : Word → Set where
  goodW-now   : ∀ {a as} (a≥∃as : a ≥∃ as) → GoodW (a ∷ as)
  goodW-later : ∀ {a as} (good-as : GoodW as) → GoodW (a ∷ as)

--
-- BadW: "bad" words.
--

BadW : List A → Set
BadW as = ¬ GoodW as

badW[] : BadW []
badW[] ()

badW-later : ∀ {a as} → ¬ a ≥∃ as → BadW as → BadW (a ∷ as)
badW-later a≱∃as badw-a∷as (goodW-now a≥∃as) =
  a≱∃as a≥∃as
badW-later a≱∃as badw-a∷as (goodW-later good-as) =
  badw-a∷as good-as

--
-- `BarW as`: eventually any continuation of `as` becomes good.
--

data BarW : Word → Set where
  barw-now   : ∀ {as} (good-as : GoodW as) → BarW as
  barw-later : ∀ {as} (l-barw : ∀ a → BarW (a ∷ as)) → BarW as

--
-- Homeomorphic embedding of words.
--

infix 4 _⊵_

data _⊵_ : Word → Word → Set where
  ⊵-[]   : [] ⊵ []
  ⊵-drop : ∀ {w v a} → w ⊵ v → a ∷ w ⊵ v
  ⊵-keep : ∀ {w v a b} → a ≥ b → w ⊵ v → a ∷ w ⊵ b ∷ v

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
  good-now   : ∀ {w ws} (w⊵∃ws : w ⊵∃ ws) → Good (w ∷ ws)
  good-later : ∀ {w ws} (good-ws : Good ws) → Good (w ∷ ws)

Bad : Seq → Set
Bad ws = ¬ Good ws

--
-- Inductive bars (for sequences of words)
-- `Bar ws`: eventually any continuation of `ws` becomes good.
--

data Bar : Seq → Set where
  now   : ∀ {ws} → (good-ws : Good ws) → Bar ws
  later : ∀ {ws} → (l-bar : ∀ w → Bar (w ∷ ws)) → Bar ws

--
-- In some papers this lemma is called "prop1".
-- (A very expressiove and informative name...) :-)
--

bar[]∷ : ∀ ws → Bar([] ∷ ws)
bar[]∷ ws = later (λ w → now (good-now (here (⊵[] w))))

--
-- Subsequences are a special case of embedding.
--

infix 4 _⋐_

data _⋐_ : (vs ws : Seq) → Set where
  ⋐-[]   : [] ⋐ []
  ⋐-drop : ∀ {vs ws w} → vs ⋐ ws → vs ⋐ w ∷ ws
  ⋐-keep : ∀ {vs ws v} → vs ⋐ ws → v ∷ vs ⋐ v ∷ ws

⋐-refl : ∀ {ws} → ws ⋐ ws
⋐-refl {[]} = ⋐-[]
⋐-refl {w ∷ ws} = ⋐-keep ⋐-refl

-- The monotonicity of _⊵∃_ and Good with respect to _⋐_ .

⊵∃-mono : ∀ {w vs ws} → vs ⋐ ws → w ⊵∃ vs → w ⊵∃ ws
⊵∃-mono ⋐-[] ()
⊵∃-mono (⋐-drop {vs} {ws} {v} vs⋐) w⊵∃ =
  there (⊵∃-mono vs⋐ w⊵∃)
⊵∃-mono (⋐-keep vs⋐) (here w⊵) =
  here w⊵
⊵∃-mono (⋐-keep vs⋐) (there w⊵∃) =
  there (⊵∃-mono vs⋐ w⊵∃)

good-mono : ∀ {vs ws} → vs ⋐ ws → Good vs → Good ws
good-mono ⋐-[] ()
good-mono (⋐-drop vs⋐) good-vs =
  good-later (good-mono vs⋐ good-vs)
good-mono (⋐-keep vs⋐) (good-now w⊵∃) =
  good-now (⊵∃-mono vs⋐ w⊵∃)
good-mono (⋐-keep vs⋐) (good-later good-vs) =
  good-later (good-mono vs⋐ good-vs)

--
-- Sorted letter sequences
--

data Sorted : List A → Set where
  sorted-[]  : Sorted []
  sorted-∷[] : ∀ {a} → Sorted (a ∷ [])
  sorted-≥   : ∀ {a b ws} → a ≥ b → Sorted (b ∷ ws) → Sorted (a ∷ b ∷ ws)

-- Zipping sequences

zip-seq : (v : List A) (ws : Seq) → Seq
zip-seq [] ws = ws
zip-seq (a ∷ v) [] = []
zip-seq (a ∷ v) (w ∷ ws) = (a ∷ w) ∷ (zip-seq v ws)

⊵∃-drop : ∀ {a w ws} → w ⊵∃ ws → (a ∷ w) ⊵∃ ws
⊵∃-drop (here w⊵v) = here (⊵-drop w⊵v)
⊵∃-drop (there w⊵∃ws) = there (⊵∃-drop w⊵∃ws)

⊵∃-zip : ∀ {v a w ws} → Sorted (a ∷ v) →
  w ⊵∃ ws → (a ∷ w) ⊵∃ (zip-seq v ws)
⊵∃-zip {[]} sorted-∷[] w⊵∃ws =
  ⊵∃-drop w⊵∃ws
⊵∃-zip {b ∷ v} (sorted-≥ a≥b sorted-b∷v) (here w⊵w′) =
  here (⊵-keep a≥b w⊵w′)
⊵∃-zip {b ∷ .[]} (sorted-≥ a≥ sorted-∷[]) (there w⊵∃) =
  there (⊵∃-zip sorted-∷[] w⊵∃)
⊵∃-zip {b ∷ ._} (sorted-≥ a≥ (sorted-≥ b≥ sorted-∷)) (there w⊵∃) =
  there (⊵∃-zip (sorted-≥ (≥-trans a≥ b≥) sorted-∷) w⊵∃)

-- Sorted v → Good ws → Good (zip-seq v ws)

good-zip : ∀ {v ws} →
  Sorted v → Good ws → Good (zip-seq v ws)
good-zip {[]} sorted-v (good-now w⊵∃ws) =
  good-now w⊵∃ws
good-zip {a ∷ v} sorted-v (good-now w⊵∃ws) =
  good-now (⊵∃-zip sorted-v w⊵∃ws)
good-zip {[]} sorted-v (good-later good-ws) =
  good-later good-ws
good-zip {a ∷ .[]} sorted-∷[] (good-later good-ws) =
  good-later good-ws
good-zip {a ∷ ._} (sorted-≥ a≥ sorted-∷) (good-later good-ws) =
  good-later (good-zip sorted-∷ good-ws)

--
-- Roots of tree nodes
--

Root = A × Word × Seq

data Tree : Set where
  ⟪_⟫_ : (r : Root) (f : List Tree) → Tree

Forest = List Tree

root : Tree → Root
root (⟪ r ⟫ f) = r

children : Tree → List Tree
children (⟪ r ⟫ f) = f

--
-- Roots in trees and forests
--

infix 4 _≪_ _≪∃_

mutual

  data _≪_ : Root → Tree → Set where
    here  : ∀ {r f} → r ≪ ⟪ r ⟫ f
    there : ∀ {r f r′} → r′ ≪∃ f → r′ ≪ (⟪ r ⟫ f)

  _≪∃_ : Root → List Tree → Set
  r ≪∃ f = Any (_≪_ r) f

-- Selecting parts of ⟪ a , w , vs ⟫ f .

label : (t : Tree) → A
label t = proj₁ (root t)

heads : (r : Root) → Word
heads r = proj₁ r ∷ proj₁ (proj₂ r)

tails : (t : Root) → Seq
tails r = proj₂ (proj₂ r)

labels : (f : Forest) → List A
labels f = List.map label f

--
-- Updating forests.
-- (This corresponds to Seisenberger's `insert-folder`.)
--

mutual

  update : ∀ f a (u : Word) (a≥∃ : a ≥∃ labels f) → Forest
  update [] a u ()
  update (t ∷ f) a u (here a≥) =
    update-tree t a u ∷ f
  update (t ∷ f) a u (there a≥∃) =
    t ∷ update f a u a≥∃

  update-tree : (t : Tree) (a : A) (u : Word) → Tree
  update-tree (⟪ b , v , vs ⟫ f) a u with a ≥∃? labels f
  ... | yes a≥∃ = ⟪ b , v , vs ⟫ update f a u a≥∃
  ... | no  a≱∃ = ⟪ b , v , vs ⟫ ((⟪ a , b ∷ v , u ∷ vs ⟫ f) ∷ f)

-- Extending forests.

extend : (a : A) (u : Word) (vs : Seq) (f : Forest) → Forest
extend a u vs f = (⟪ a , [] , u ∷ vs ⟫ f) ∷ f

--
-- Building a forest from a word sequence.
-- (Here Seisenberger defines a function, but we use a relation.)
--

data Build : Seq → Forest → Set where
  bld-[] : Build [] []
  bld-≱ : ∀ {a w ws f}
    (bld : Build ws f)
    (a≱∃ : ¬ a ≥∃ labels f) →
    Build ((a ∷ w) ∷ ws) (extend a w ws f)
  bld-≥ : ∀ {a w ws f}
    (bld : Build ws f)
    (a≥∃ : a ≥∃ labels f) →
    Build ((a ∷ w) ∷ ws) (update f a w a≥∃)

--
-- Updating a forest does not change its top-level labels.
--

labels∘update≡ :
  ∀ f a v (a≥∃ : a ≥∃ labels f) →
    labels (update f a v a≥∃) ≡ labels f
labels∘update≡ [] a v ()
labels∘update≡ (⟪ r ⟫ f′ ∷ f) a v (here a≥) with a ≥∃? labels f′
... | yes a≥∃ = refl
... | no  a≱∃ = refl
labels∘update≡ (t ∷ f) a v (there a≥∃) =
  cong₂ _∷_ refl (labels∘update≡ f a v a≥∃)

bs≡→bs≡upd : ∀ f a v (a≥∃ : a ≥∃ labels f) {bs} →
  bs ≡ labels f →
  bs ≡ labels (update f a v a≥∃)
bs≡→bs≡upd f a v a≥∃ {bs} bs≡ = begin
  bs
    ≡⟨ bs≡ ⟩
  labels f
    ≡⟨ sym $ labels∘update≡ f a v a≥∃ ⟩
  labels (update f a v a≥∃)
  ∎
  where open ≡-Reasoning

--
-- `zip-root r` restores the sequence represented by `r`.
--

zip-root : Root → Seq
zip-root ( a , as , vs ) = zip-seq (a ∷ as) vs

RZip⋐ : Root → Seq → Set
RZip⋐ r ws = zip-root r ⋐ ws

TZip⋐ : Tree → Seq → Set
TZip⋐ t ws = ∀ {r} → r ≪ t → zip-root r ⋐ ws

FZip⋐ : Forest → Seq → Set
FZip⋐ f ws = ∀ {r} → r ≪∃ f → zip-root r ⋐ ws

--
-- A forest, built from ws, represents subsequences of ws.
--
--   Build ws f → FZip⋐ f ws
--

zip⋐⟪⟫ : ∀ {ws r f} → RZip⋐ r ws → FZip⋐ f ws → TZip⋐ (⟪ r ⟫ f) ws
zip⋐⟪⟫ hr hf here = hr
zip⋐⟪⟫ hr hf (there r′′≪) = hf r′′≪

zip⋐∷ : ∀ {ws t f} → TZip⋐ t ws → FZip⋐ f ws → FZip⋐ (t ∷ f) ws
zip⋐∷ ht hf (here r≪) = ht r≪
zip⋐∷ ht hf (there r≪∃) = hf r≪∃

zip⋐upd : ∀ {f ws a u} →
  (a≥∃ : a ≥∃ labels f) →
  FZip⋐ f ws → FZip⋐ (update f a u a≥∃) ((a ∷ u) ∷ ws)
zip⋐upd {[]} () h t′≪
zip⋐upd {⟪ r′ ⟫ f′ ∷ f} {ws} {a} (here a≥) h (here r≪)
  with a ≥∃? labels f′
... | yes a≥∃ =
  zip⋐⟪⟫ (⋐-drop (h (here here))) (zip⋐upd a≥∃ (h ∘′ here ∘′ there)) r≪
... | no  a≱∃ =
  zip⋐⟪⟫ (⋐-drop (h (here here)))
          (zip⋐∷ (zip⋐⟪⟫ (⋐-keep (h (here here)))
                           (⋐-drop ∘′ h ∘′ here ∘′ there))
                 (⋐-drop ∘′ h ∘′ here ∘′ there))
          r≪
zip⋐upd {t ∷ f} (here a≥) h (there r≪) =
  ⋐-drop (h (there r≪))
zip⋐upd {t ∷ f} (there a≥∃) h (here r≪) =
 ⋐-drop (h (here r≪))
zip⋐upd {t ∷ f} (there a≥∃) h (there r≪) =
  zip⋐upd a≥∃ (h ∘ there) r≪

bld→zip⋐ : ∀ {ws f} →
  Build ws f → FZip⋐ f ws
bld→zip⋐ bld-[] ()
bld→zip⋐ (bld-≱ bld a≱∃) (here here) =
  ⋐-refl
bld→zip⋐ (bld-≱ bld a≱∃) (here (there r≪∃)) =
  ⋐-drop (bld→zip⋐ bld r≪∃)
bld→zip⋐ (bld-≱ bld a≱∃) {a , as , vs} (there r≪∃) =
  ⋐-drop (bld→zip⋐ bld r≪∃)
bld→zip⋐ (bld-≥ bld a≥∃) r≪ =
  zip⋐upd a≥∃ (bld→zip⋐ bld) r≪


--
-- Build ws f → ∀ r → r ≪∃ f → Sorted (heads r)
--

RSorted : Root → Set
RSorted r = Sorted (heads r)

TSorted : Tree → Set
TSorted t = ∀ {r} → r ≪ t → RSorted r 

FSorted : Forest → Set
FSorted f = ∀ {r} → r ≪∃ f → RSorted r 

sorted-⟪⟫ : ∀ {r f} → RSorted r → FSorted f → TSorted (⟪ r ⟫ f)
sorted-⟪⟫ hr hf here = hr
sorted-⟪⟫ hr hf (there r≪∃) = hf r≪∃

sorted-∷ : ∀ {t f} → TSorted t → FSorted f → FSorted (t ∷ f)
sorted-∷ ht hf (here r≪) = ht r≪
sorted-∷ ht hf (there r≪∃) = hf r≪∃

sorted-upd : ∀ {f a u} →
  (a≥∃ : a ≥∃ labels f) →
  FSorted f → FSorted (update f a u a≥∃)
sorted-upd {[]} () h r≪
sorted-upd {⟪ r′ ⟫ f′ ∷ f} {a} {u} (here a≥) h (here r≪)
  with a ≥∃? labels f′
... | yes a≥∃ =
  sorted-⟪⟫ (h (here here)) (sorted-upd a≥∃ (h ∘′ here ∘′ there)) r≪
... | no  a≱∃ =
  sorted-⟪⟫ (h (here here))
            (sorted-∷ (sorted-⟪⟫ (sorted-≥ a≥ (h (here here)))
                                 (h ∘′ here ∘′ there))
                      (h ∘′ here ∘′ there))
            r≪
sorted-upd {t ∷ f} (here a≥) h (there r≪∃) =
  h (there r≪∃)
sorted-upd {t ∷ f} (there a≥∃) h (here r≪) =
  h (here r≪)
sorted-upd {t ∷ f} (there a≥∃) h (there r≪∃) =
  sorted-upd a≥∃ (h ∘′ there) r≪∃

bld→sorted-heads : ∀ {f ws} →
  Build ws f → FSorted f
bld→sorted-heads bld-[] ()
bld→sorted-heads (bld-≱ bld a≱∃) (here here) =
  sorted-∷[]
bld→sorted-heads (bld-≱ bld a≱∃) {r} (here (there r≪∃)) =
  bld→sorted-heads bld r≪∃
bld→sorted-heads (bld-≱ bld a≱∃) {r} (there r≪∃) =
  bld→sorted-heads bld r≪∃
bld→sorted-heads (bld-≥ bld a≥∃) r≪∃ =
  sorted-upd a≥∃ (bld→sorted-heads bld) r≪∃

--
-- good∈folder→good
--
-- This lemma corresponds to Lemma 5.7i in Seisenberger's thesis
-- (where it is just assumed to be true "by construction").
-- However, writing out an accurate formalized proof does take
-- some effort.
--

good∈forest→good : ∀ {ws f}
  (bld : Build ws f)
  {r} (r≪∃ : r ≪∃ f)
  (good-r : Good (tails r)) →
  Good ws

good∈forest→good {ws} {f} bld {r} r≪∃ good-r =
  helper good-r
  where
  v = heads r
  vs = tails r

  sorted-v : Sorted v
  sorted-v = bld→sorted-heads bld r≪∃

  zip⋐ws : zip-seq v vs ⋐ ws
  zip⋐ws = bld→zip⋐ bld r≪∃

  good-zip-v-vs : Good (zip-seq v vs)
  good-zip-v-vs = good-zip sorted-v good-r

  open Related.EquationalReasoning
  helper =
    Good vs
      ∼⟨ good-zip sorted-v ⟩
    Good (zip-seq v vs)
      ∼⟨ good-mono zip⋐ws ⟩
    Good ws
    ∎

--
-- What is "Bar forest"?
--

data Bars : Forest → Set where
  bars-now   : ∀ {f r}
    (r≪∃ : r ≪∃ f) →
    (good-r : Good (tails r)) →
    Bars f
  bars-later : ∀ {f}
    (l : ∀ {a} v (a≥∃ : a ≥∃ labels f) → Bars (update f a v a≥∃)) →
    Bars f

--
-- Build ws f → BadW (labels f)
--

bld→bad-as : ∀ {ws f} →
  Build ws f → ∀ {as} → as ≡ labels f → BadW as
bld→bad-as bld-[] refl ()
bld→bad-as (bld-≱ bld a≱∃) refl (goodW-now a≥∃) =
  ⊥-elim (a≱∃ a≥∃)
bld→bad-as (bld-≱ bld a≱∃) refl (goodW-later good-as) =
  bld→bad-as bld refl good-as
bld→bad-as (bld-≥ {a} {w} {ws} {f} bld a≥∃) refl good-as
  rewrite labels∘update≡ f a w a≥∃
  = bld→bad-as bld refl good-as

--
-- Extending a forest with a new tree, while preserving
-- the invariant `Bars f`.
--

mutual

  bars∷ : ∀ {t f} → Bars (t ∷ []) → Bars f → Bars (t ∷ f)
  bars∷ (bars-now (here r≪t) good-r) bars-f =
    bars-now (here r≪t) good-r
  bars∷ (bars-now (there ()) good-t) bars-f
  bars∷ {t} {f} (bars-later l-bar-t) bars-f =
    bars∷₁ l-bar-t bars-f

  bars∷₁ : ∀ {t f} →
    (∀ {a} v a≥∃ → Bars (update (t ∷ []) a v a≥∃)) →
    Bars f → Bars (t ∷ f)
  bars∷₁ l-bar-t (bars-now r≪∃ good-r) =
    bars-now (there r≪∃) good-r
  bars∷₁ {t} {f} l-bar-t (bars-later l-bar-f) =
    bars-later helper
    where helper : ∀ {a} v (a≥∃ : a ≥∃ labels (t ∷ f)) →
                     Bars (update (t ∷ f) a v a≥∃)
          helper v (here a≥) =    -- update-tree t a v ∷ f
            bars∷ (l-bar-t v (here a≥)) (bars-later l-bar-f)
          helper v (there a≥∃) =  -- t ∷ update f a v a≥∃
            bars∷₁ l-bar-t (l-bar-f v a≥∃)

mutual

  bars∷[] : ∀ {a v ws f bs} →
    bs ≡ labels f → BadW bs →
    BarW bs → Bar ws → Bars f →
    Bars (⟪ a , v , ws ⟫ f ∷ [])
  bars∷[] bs≡ bad-bs (barw-now good-bs) bar-ws bars-f =
    ⊥-elim (bad-bs good-bs)
  bars∷[] bs≡ bad-bs (barw-later l-barw) bar-ws bars-f =
    bars∷[]₁ bs≡ bad-bs l-barw bar-ws bars-f

  bars∷[]₁ : ∀ {a v ws f bs} →
    bs ≡ labels f → BadW bs →
    (∀ b → BarW (b ∷ bs)) → Bar ws → Bars f →
    Bars (⟪ a , v , ws ⟫ f ∷ [])
  bars∷[]₁ bs≡ bad-bs l-barw (now good-ws) bars-f =
    bars-now (here here) good-ws
  bars∷[]₁ bs≡ bad-bs l-barw (later l-bar) bars-f =
    bars∷[]₂ bs≡ bad-bs l-barw l-bar bars-f

  bars∷[]₂ : ∀ {a v ws f bs} →
    bs ≡ labels f → BadW bs →
    (∀ b → BarW (b ∷ bs)) → (∀ w → Bar (w ∷ ws)) → Bars f →
    Bars (⟪ a , v , ws ⟫ f ∷ [])
  bars∷[]₂ bs≡ bad-bs l-barw l-bar (bars-now r≪∃ good-r) =
    bars-now (here (there r≪∃)) good-r
  bars∷[]₂ {a} {v} {ws} {f} {bs} bs≡ bad-bs l-barw l-bar (bars-later l-bars) =
    bars-later helper
    where
    helper : ∀ {b} w a≥∃ → Bars (update (⟪ a , v , ws ⟫ f ∷ []) b w a≥∃)
    helper w (there ())
    helper {b} w (here b≥a) with b ≥∃? labels f
    ... | yes b≥∃ =
      Bars (⟪ a , v , ws ⟫ update f b w b≥∃ ∷ []) ∋
      bars∷[]₂ (bs≡→bs≡upd f b w b≥∃ bs≡)
               bad-bs l-barw l-bar (l-bars w b≥∃)
    ... | no  b≱∃ =
      Bars (⟪ a , v , ws ⟫ (⟪ b , a ∷ v , w ∷ ws ⟫ f ∷ f) ∷ []) ∋
      bars∷[] (cong (_∷_ b) bs≡)
              (badW-later (λ b≥∃ → b≱∃ (subst (_≥∃_ b) bs≡ b≥∃)) bad-bs)
              (l-barw b) (later l-bar)
              (bars∷ (bars∷[]₁ bs≡ bad-bs
                               l-barw (l-bar w) (bars-later l-bars))
                     (bars-later l-bars))


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
    BarW as → Bars f → Bar ws
  higman₀ ws f bld as≡ (barw-now good-as) bars-f =
    ⊥-elim (bld→bad-as bld as≡ good-as)
  higman₀ ws f bld as≡ (barw-later l-barw) bars-f =
    higman₁ ws f bld as≡ l-barw bars-f

  -- If `Bars f` contains (a representation of) a good subsequence,
  -- then ws is good. Hence, `Bar ws`.
  -- Otherwise, `∀ a v a≥∃ → Bars (update f a v a≥∃)`.

  higman₁ : ∀ ws f →
    Build ws f → ∀ {as} → as ≡ labels f →
    (∀ a → BarW (a ∷ as)) → Bars f → Bar ws
  higman₁ ws f bld as≡ l-barw (bars-now r≪∃ good-r) =
    now (good∈forest→good bld r≪∃ good-r)
  higman₁ ws f bld as≡ l-barw (bars-later l-bars) =
    later (λ w → higman₂ w ws f bld as≡ l-barw l-bars)

  -- Now the word sequence *is not empty*.
  -- Hence, let's do induction on the first word of the sequence.

  higman₂ : ∀ (w : Word) ws f →
    Build ws f → ∀ {as} → as ≡ labels f →
    (∀ a → BarW (a ∷ as)) →
    (∀ {a} v a≥∃ → Bars (update f a v a≥∃)) →
    Bar (w ∷ ws)

  -- []. Bars ([] ∷ ws).
  higman₂ [] ws f bld as≡ l-barw l-bars =
    bar[]∷ ws

  -- a ∷ w.
  higman₂ (a ∷ w) ws f bld {as} as≡ l-barw l-bars
    with a ≥∃? as
  ... | yes a≥∃as =
    -- a ≥∃ labels f. f is updated to f′.
    -- So, `labels f ≡ labels f′`.
    higman₁ ((a ∷ w) ∷ ws) (update f a w a≥∃)
            (bld-≥ bld a≥∃) (bs≡→bs≡upd f a w a≥∃ as≡)
            l-barw (l-bars w a≥∃)
    where
      a≥∃ = a ≥∃ as ∼⟨ subst (_≥∃_ a) as≡ ⟩ a ≥∃ labels f ∎ $ a≥∃as
        where open Related.EquationalReasoning

  ... | no  a≱∃as =
    -- a ≱∃ labels f. f is extended to f′.
    -- So, a ∷ labels f ≡  labels f′.
    higman₀ ((a ∷ w) ∷ ws) (extend a w ws f)
            (bld-≱ bld a≱∃)
            (cong (_∷_ a) as≡)
            (l-barw a)
            (bars∷ (bars∷[] as≡ (bld→bad-as bld as≡)
                            (barw-later l-barw)
                            (higman₂ w ws f bld as≡ l-barw l-bars)
                            (bars-later l-bars))
                    (bars-later l-bars))
    where
      a≱∃ : ¬ a ≥∃ labels f
      a≱∃ = a ≥∃ labels f  ∼⟨ subst (_≥∃_ a) (P.sym $ as≡) ⟩
            a ≥∃ as ∼⟨ a≱∃as ⟩ ⊥ ∎
        where open Related.EquationalReasoning

--
-- bars[]
--

bars[] : Bars []
bars[] = bars-later helper
  where helper : ∀ {a} v a≥∃ → Bars (update [] a v a≥∃)
        helper v ()

--
-- higman
--

higman : BarW [] → Bar []
higman barW[] = higman₀ [] [] bld-[] refl barW[] bars[]
