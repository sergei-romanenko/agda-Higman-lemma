{-
    Title:      Higman.Agda
    Author:     Sergei Romanenko, KIAM Moscow

    This version is produced by rewriting the proof presented in

      S. Berghofer. A constructive proof of Higman's lemma in Isabelle.
      In Types for Proofs and Programs, TYPES'04. LNCS, 3085: 66-82.
      Springer Verlag, 2004. 

    from Isabelle to Agda.
-}

module Higman where

open import Data.Nat
  using (ℕ; zero; suc)
open import Data.Bool
  using (Bool; true; false; _≟_; not)
open import Data.Bool.Properties
  using (¬-not; not-¬)
open import Data.List as List
  hiding (any; all)
open import Data.List.Any as Any
  using (Any; here; there; any; module Membership; module Membership-≡)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using(⊥; ⊥-elim)

open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  renaming([_] to ≡[_])

-- Words are modelled as lists of letters from
-- the two letter alphabet.

Letter : Set
Letter = Bool

Word = List Letter
Seq = List Word

-- The embedding relation on words is defined inductively.
-- Intuitively, a word `v` can be embedded into a word `w`,
-- if we can obtain `v` by deleting letters from `w`.
-- For example,
--   false ∷ true ∷ false ∷ true ∷ [] ⊵ true ∷ true ∷ []

infix 4 _⊵_ _⊵∃_

data _⊵_ : Word → Word → Set where
  ⊵-[]   : [] ⊵ []
  ⊵-drop : ∀ {w v a} → w ⊵ v → a ∷ w ⊵ v
  ⊵-keep : ∀ {w v a} → w ⊵ v → a ∷ w ⊵ a ∷ v

-- [] is embeddable in any word.

⊵[] : ∀ w → w ⊵ []
⊵[] [] = ⊵-[]
⊵[] (a ∷ w) = ⊵-drop (⊵[] w)

-- In order to formalize the notion of a good sequence,
-- it is useful to define an auxiliary relation _⊵∃_.
--   v ⊵∃ ws
-- means that ws contains a word w, such that v ⊵ w .

_⊵∃_ : (w : Word) (ws : Seq) → Set
w ⊵∃ ws = Any (_⊵_ w) ws

-- A list of words is good if its tail is either good
-- or contains a word which can be embedded into the word
-- occurring at the head position of the list.

data Good : List Word → Set where
  good-now   : ∀ {ws w} (n : w ⊵∃ ws) → Good (w ∷ ws)
  good-later : ∀ {ws w} (l : Good ws) → Good (w ∷ ws)

-- In order to express the fact that every infinite sequence is good,
-- we define a predicate Bar.
--
-- Intuitively, Bar ws means that either
-- (1) the list of words ws is already good, or
-- (2) successively adding words will turn it into a good list.

data Bar : List Word → Set where
  now   : ∀ {ws} (g : Good ws) → Bar ws
  later : ∀ {ws} (l : ∀ w → Bar (w ∷ ws)) → Bar ws

-- Consequently,
--   Bar []
-- means that every infinite sequence must be good,
-- since by successively adding words to the empty list, we must
-- eventually arrive at a list which is good.

-- (Note that the above definition of Bar is closely related to
-- Brouwer’s more general principle of bar induction.)


-- The following function adds a letter to each word in a word list. 

infixr 5 _∷∈_

_∷∈_ : (a : Letter) (ws : List Word) → List Word
a ∷∈ ws = map (_∷_ a) ws

-- `T a vs ws` means that vs is obtained from ws by
-- (1) first copying the prefix of words starting with the letter b,
--     where a ≢ b, and
-- (2) then appending the tails of words starting with a.

data T (a : Letter) : List Word → List Word → Set where
  t-init : ∀ {v ws b} → (a≢b : a ≢ b) →
           T a (v ∷ b ∷∈ ws) ((a ∷ v) ∷ b ∷∈ ws)
  t-keep : ∀ {v vs ws} →
           (t : T a vs ws) → T a (v ∷ vs) ((a ∷ v) ∷ ws)
  t-drop : ∀ {v vs ws b} → (a≢b : a ≢ b) →
           (t : T a vs ws) → T a vs ((b ∷ v) ∷ ws)
  t-[]   : T a [] []  -- This rule ensures that `T a ws (a ∷∈ ws)` for all `ws`.

-- Auxiliaries

≢-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
≢-sym x≢y y≡x = x≢y (sym y≡x)

≢-trans : ∀ {x y z : Letter} →
            x ≢ y → y ≢ z → x ≡ z
≢-trans  {x} {y} {z} x≢y y≢z = begin
  x ≡⟨ ¬-not x≢y ⟩ not y ≡⟨ sym (¬-not (≢-sym y≢z)) ⟩ z ∎
  where open ≡-Reasoning

--
-- The proof of Higman’s lemma is divided into several parts, namely
-- prop1, prop2 and prop3.
-- From the computational point of view, these theorems can be thought of
-- as functions transforming trees.

--
-- prop1 : Sequences “ending” with empty word (trivial)
-- A sequence ending with the empty word satisfies predicate Bar,
-- since it can trivially be extended to a good sequence
-- by appending any word.
--

bar[]∷ : (ws : List Word) → Bar ([] ∷ ws)
bar[]∷ ws = later (λ w → now (good-now (here (⊵[] w))))

-- Lemmas. w ⊵∃ ... → (a ∷ w) ⊵∃ ...

⊵∃-drop : ∀ {ws a w} → w ⊵∃ ws → a ∷ w ⊵∃ ws
⊵∃-drop (here w⊵) = here (⊵-drop w⊵)
⊵∃-drop (there w⊵∃) = there (⊵∃-drop w⊵∃)

⊵∃-∷∈ : ∀ {ws a w} → w ⊵∃ ws → a ∷ w ⊵∃ a ∷∈ ws
⊵∃-∷∈ {[]} ()
⊵∃-∷∈ {_ ∷ _} (here w⊵) = here (⊵-keep w⊵)
⊵∃-∷∈ {_ ∷ _} (there w⊵∃) = there (⊵∃-∷∈ w⊵∃)

t-⊵∃-drop : ∀ {a v vs ws} → T a vs ws → v ⊵∃ vs → a ∷ v ⊵∃ ws
t-⊵∃-drop (t-init a≢b) (here v⊵) = here (⊵-keep v⊵)
t-⊵∃-drop (t-init a≢b) (there v⊵∃) = there (⊵∃-drop v⊵∃)
t-⊵∃-drop (t-keep t) (here v⊵) = here (⊵-keep v⊵)
t-⊵∃-drop (t-keep t) (there v⊵∃) = there (t-⊵∃-drop t v⊵∃)
t-⊵∃-drop (t-drop a≢b t) v⊵∃ = there (t-⊵∃-drop t v⊵∃)

-- Lemmas. Good ... → Good ...

good-∷∈ : ∀ {a ws} → Good ws → Good (a ∷∈ ws)
good-∷∈ (good-now n) = good-now (⊵∃-∷∈ n)
good-∷∈ (good-later l) = good-later (good-∷∈ l)

t-good : ∀ {a vs ws} → T a vs ws → Good vs → Good ws
t-good (t-init a≢b) (good-now n) = good-now (⊵∃-drop n)
t-good (t-init a≢b) (good-later l) = good-later l
t-good (t-keep t) (good-now n) = good-now (t-⊵∃-drop t n)
t-good (t-keep t) (good-later l) = good-later (t-good t l)
t-good (t-drop a≢b t) g = good-later (t-good t g)

-- Lemma. T a (...) (a ∷∈ ...)

t-∷∈ : ∀ a ws → T a ws (a ∷∈ ws)
t-∷∈ a [] = t-[]
t-∷∈ a (v ∷ []) = t-init (not-¬ refl)
t-∷∈ a (v ∷ w ∷ ws) = t-keep (t-∷∈ a (w ∷ ws))

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
-- then case distinction on first letter of first word following zs

mutual

  ttBar : ∀ {zs a b xs ys} → a ≢ b → T a xs zs → T b ys zs →
            Bar xs → Bar ys → Bar zs

  ttBar a≢b ta tb (now gx) by = now (t-good ta gx)
  ttBar a≢b ta tb (later lx) by = ttBar₁ a≢b ta tb lx by

  ttBar₁ : ∀ {zs a b xs ys} → a ≢ b → T a xs zs → T b ys zs →
             (∀ w → Bar (w ∷ xs)) → Bar ys → Bar zs

  ttBar₁ a≢b ta tb lx (now gy) = now (t-good tb gy)
  ttBar₁ a≢b ta tb lx (later ly) = later (ttBar₂ a≢b ta tb lx ly)

  ttBar₂ : ∀ {zs a b xs ys} → a ≢ b → T a xs zs → T b ys zs →
             (∀ w → Bar (w ∷ xs)) → (∀ w → Bar (w ∷ ys)) →
             (∀ w → Bar (w ∷ zs))

  ttBar₂ {zs} a≢b ta tb lx ly [] = bar[]∷ zs
  ttBar₂ {zs} {a} {b} {xs} {ys} a≢b ta tb lx ly (c ∷ v) with c ≟ a
  ... | yes c≡a rewrite c≡a =
    Bar ((a ∷ v) ∷ zs) ∋
    ttBar a≢b
          (T a (v ∷ xs) ((a ∷ v) ∷ zs)
            ∋ t-keep ta)
          (T b ys ((a ∷ v) ∷ zs)
            ∋ t-drop (≢-sym a≢b) tb)
          ({- Bar (v ∷ xs)
            ∋ -} lx v)
          (Bar ys
            ∋ later ly)
  ... | no  c≢a rewrite c ≡ b ∋ ≢-trans c≢a a≢b =
    Bar ((b ∷ v) ∷ zs) ∋
    ttBar₁ a≢b
           (T a xs ((b ∷ v) ∷ zs)
             ∋ t-drop a≢b ta)
           (T b (v ∷ ys) ((b ∷ v) ∷ zs)
             ∋ t-keep tb)
           ({- (∀ w → Bar (w ∷ xs))
             ∋ -} lx)
           ({- Bar (v ∷ ys)
             ∋ -} ly v)


--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar xs, then induction on first word following zs

mutual

  bar∷∈ : ∀ {a ws} → Bar ws → Bar (a ∷∈ ws)

  bar∷∈ (now g) = now (good-∷∈ g)
  bar∷∈ (later l) = later (bar∷∈₁ l)

  bar∷∈₁ : ∀ {a ws} → (∀ w → Bar (w ∷ ws)) → (∀ w → Bar (w ∷ a ∷∈ ws))

  bar∷∈₁ {a} {ws} l [] = bar[]∷ (a ∷∈ ws)
  bar∷∈₁ {a} {ws} l (b ∷ v) with b ≟ a
  ... | yes b≡a rewrite b≡a =
    Bar (a ∷∈ (v ∷ ws)) ∋
    bar∷∈ (l v)
  ... | no  b≢a =
    Bar ((b ∷ v) ∷ a ∷∈ ws) ∋
    ttBar b≢a
          (T b (v ∷ a ∷∈ ws) ((b ∷ v) ∷ a ∷∈ ws)
            ∋ t-init b≢a)
          (T a ws ((b ∷ v) ∷ a ∷∈ ws)
            ∋ t-drop (≢-sym b≢a) (t-∷∈ a ws))
          (Bar (v ∷ a ∷∈ ws)
            ∋ bar∷∈₁ l v)
          (Bar ws
            ∋ later l)


--
-- higman: Main theorem
--

higman′ :  ∀ w → Bar (w ∷ [])
higman′ [] = bar[]∷ []
higman′ (c ∷ cs) = bar∷∈ (higman′ cs)

higman : Bar []
higman = later higman′


--
-- good-prefix-lemma
--

data Is-prefix {A : Set} (f : ℕ → A) : List A → Set where
  zero : Is-prefix f []
  suc  : ∀ {xs : List A} →
        Is-prefix f xs → Is-prefix f (f (length xs) ∷ xs)

test-is-prefix : Is-prefix (λ k → suc (suc k)) (4 ∷ 3 ∷ 2 ∷ [])
test-is-prefix = suc (suc (suc zero))

good-prefix-lemma :
  ∀ (f : ℕ → Word) ws →
    Bar ws → Is-prefix f ws →
    ∃ λ vs → Is-prefix f vs × Good vs
good-prefix-lemma f ws (now g) p =
  ws , p , g
good-prefix-lemma f ws (later l) p =
  let w = f (length ws)
  in good-prefix-lemma f (w ∷ ws) (l w) (suc p)

-- Finding good prefixes of infinite sequences

good-prefix :
  ∀ (f : ℕ → Word) →
    ∃ λ ws → (Is-prefix f ws × Good ws)
good-prefix f = good-prefix-lemma f [] higman zero
