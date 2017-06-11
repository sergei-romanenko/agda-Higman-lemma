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
  using (not-¬)
open import Data.List as List
  hiding (any; all)
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

infix 4 _⊴_ _∋⊴_

data _⊴_ : (v w : Word) → Set where
  ⊴-[]   : [] ⊴ []
  ⊴-drop : ∀ {v w a} → v ⊴ w → v ⊴ a ∷ w
  ⊴-keep : ∀ {v w a} → v ⊴ w → a ∷ v ⊴ a ∷ w

-- [] is embeddable in any word.

[]⊴ : ∀ w → [] ⊴ w
[]⊴ [] = ⊴-[]
[]⊴ (a ∷ w) = ⊴-drop ([]⊴ w)

-- In order to formalize the notion of a good sequence,
-- it is useful to define an auxiliary relation _⊵∃_.
--   ws ∋⊴ v
-- means that ws contains a word w, such that w ⊴ v .

data _∋⊴_ : (ws : Seq) (v : Word) → Set where
  here  : ∀ {w ws v} (w⊴v : w ⊴ v) → w ∷ ws ∋⊴ v
  there : ∀ {w ws v} (ws∋⊴v : ws ∋⊴ v) → w ∷ ws ∋⊴ v

-- A list of words is good if its tail is either good
-- or contains a word which can be embedded into the word
-- occurring at the head position of the list.

data Good : (ws : List Word) → Set where
  here  : ∀ {ws w} (ws∋⊴w : ws ∋⊴ w) → Good (w ∷ ws)
  there : ∀ {ws w} (good-ws : Good ws) → Good (w ∷ ws)

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
a ∷∈ [] = []
a ∷∈ w ∷ ws = (a ∷ w) ∷ a ∷∈ ws

-- `T a vs ws` means that vs is obtained from ws by
-- (1) first copying the prefix of words starting with the letter b,
--     where a ≢ b, and
-- (2) then appending the tails of words starting with a.

data T (a : Letter) : (vs ws : List Word) → Set where
  t-init : ∀ {v ws b} → (a≢b : a ≢ b) →
           T a (v ∷ b ∷∈ ws) ((a ∷ v) ∷ b ∷∈ ws)
  t-keep : ∀ {v vs ws} →
           (t : T a vs ws) → T a (v ∷ vs) ((a ∷ v) ∷ ws)
  t-drop : ∀ {v vs ws b} → (a≢b : a ≢ b) →
           (t : T a vs ws) → T a vs ((b ∷ v) ∷ ws)
  t-[]   : T a [] []  -- This rule ensures that `T a ws (a ∷∈ ws)` for all `ws`.

--
-- Dirichlet's (pigeonhole) principle for 2 holes.
--

dirichlet2 : ∀ {a b : Letter} → a ≢ b → ∀ c → c ≡ a ⊎ c ≡ b

dirichlet2 {true}  {true}  a≢b c = ⊥-elim (a≢b refl)
dirichlet2 {false} {false} a≢b c = ⊥-elim (a≢b refl)
dirichlet2 {true}  {false} a≢b true  = inj₁ refl
dirichlet2 {true}  {false} a≢b false = inj₂ refl
dirichlet2 {false} {true}  a≢b false = inj₁ refl
dirichlet2 {false} {true}  a≢b true  = inj₂ refl

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

bar-[]∷ : (ws : List Word) → Bar ([] ∷ ws)
bar-[]∷ ws = later (λ w → now (here (here ([]⊴ w))))

-- Lemmas. w ⊵∃ ... → (a ∷ w) ⊵∃ ...

∋⊴-drop : ∀ {ws a v} → ws ∋⊴ v → ws ∋⊴ a ∷ v
∋⊴-drop (here w⊴v) = here (⊴-drop w⊴v)
∋⊴-drop (there ws∋⊴v) = there (∋⊴-drop ws∋⊴v)

∋⊴-∷∈ : ∀ {ws a v} → ws ∋⊴ v → a ∷∈ ws ∋⊴ a ∷ v
∋⊴-∷∈ (here w⊴v) = here (⊴-keep w⊴v)
∋⊴-∷∈ (there ws∋⊴v) = there (∋⊴-∷∈ ws∋⊴v)

t-∋⊴-drop : ∀ {a v vs ws} → T a vs ws → vs ∋⊴ v → ws ∋⊴ a ∷ v
t-∋⊴-drop (t-init a≢b) (here w⊴v) = here (⊴-keep w⊴v)
t-∋⊴-drop (t-init a≢b) (there vs∋⊴v) = there (∋⊴-drop vs∋⊴v)
t-∋⊴-drop (t-keep t) (here w⊴v) = here (⊴-keep w⊴v)
t-∋⊴-drop (t-keep t) (there vs∋⊴v) = there (t-∋⊴-drop t vs∋⊴v)
t-∋⊴-drop (t-drop a≢b t) vs∋⊴v = there (t-∋⊴-drop t vs∋⊴v)
t-∋⊴-drop t-[] ()

-- Lemmas. Good ... → Good ...

good-∷∈ : ∀ {a ws} → Good ws → Good (a ∷∈ ws)
good-∷∈ (here ws∋⊴w) = here (∋⊴-∷∈ ws∋⊴w)
good-∷∈ (there good-ws) = there (good-∷∈ good-ws)

t-good : ∀ {a vs ws} → T a vs ws → Good vs → Good ws
t-good (t-init a≢b) (here b-ws∋⊴v) = here (∋⊴-drop b-ws∋⊴v)
t-good (t-init a≢b) (there good-b-vs) = there good-b-vs
t-good (t-keep t) (here vs∋⊴v) = here (t-∋⊴-drop t vs∋⊴v)
t-good (t-keep t) (there good-vs) = there (t-good t good-vs)
t-good (t-drop a≢b t) good-vs = there (t-good t good-vs)
t-good t-[] ()

-- Lemma. T a (...) (a ∷∈ ...)

t-∷∈ : ∀ a vs → T a vs (a ∷∈ vs)
t-∷∈ a [] = t-[]
t-∷∈ a (v ∷ []) = t-init (not-¬ refl)
t-∷∈ a (v ∷ w ∷ vs) = t-keep (t-∷∈ a (w ∷ vs))

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

  ttBar₂ {zs} a≢b ta tb lx ly [] = bar-[]∷ zs
  ttBar₂ {zs} {a} {b} {xs} {ys} a≢b ta tb lx ly (c ∷ v) with dirichlet2 a≢b c
  ... | inj₁ c≡a rewrite c≡a =
    Bar ((a ∷ v) ∷ zs) ∋
    ttBar a≢b
          (T a (v ∷ xs) ((a ∷ v) ∷ zs)
            ∋ t-keep ta)
          (T b ys ((a ∷ v) ∷ zs)
            ∋ t-drop (a≢b ∘ sym) tb)
          ({- Bar (v ∷ xs)
            ∋ -} lx v)
          (Bar ys
            ∋ later ly)
  ... | inj₂  c≡b rewrite c≡b =
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
-- Proof idea: Induction on Bar ws, then induction on first word following ws

mutual

  bar-∷∈ : ∀ {a ws} → Bar ws → Bar (a ∷∈ ws)

  bar-∷∈ (now g) = now (good-∷∈ g)
  bar-∷∈ (later l) = later (bar-∷∈₁ l)

  bar-∷∈₁ : ∀ {a ws} → (∀ w → Bar (w ∷ ws)) → (∀ w → Bar (w ∷ a ∷∈ ws))

  bar-∷∈₁ {a} {ws} l [] = bar-[]∷ (a ∷∈ ws)
  bar-∷∈₁ {a} {ws} l (b ∷ v) with b ≟ a
  ... | yes b≡a rewrite b≡a =
    Bar (a ∷∈ (v ∷ ws)) ∋
    bar-∷∈ (l v)
  ... | no  b≢a =
    Bar ((b ∷ v) ∷ a ∷∈ ws) ∋
    ttBar b≢a
          (T b (v ∷ a ∷∈ ws) ((b ∷ v) ∷ a ∷∈ ws)
            ∋ t-init b≢a)
          (T a ws ((b ∷ v) ∷ a ∷∈ ws)
            ∋ t-drop (b≢a ∘ sym) (t-∷∈ a ws))
          (Bar (v ∷ a ∷∈ ws)
            ∋ bar-∷∈₁ l v)
          (Bar ws
            ∋ later l)


--
-- higman: Main theorem
--

higman′ :  ∀ w → Bar (w ∷ [])
higman′ [] = bar-[]∷ []
higman′ (c ∷ cs) = bar-∷∈ (higman′ cs)

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
