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
  using (Bool; true; false)
open import Data.List as List
  hiding (any; all)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)

open import Function
  using (_$_; _∋_)

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
  now   : ∀ {ws} (n : Good ws) → Bar ws
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

-- Inequality of letters.

infix 4 _<>_

data _<>_ : (a b : Letter) → Set where
  f<>t : false <> true
  t<>f : true <> false

<>-sym : ∀ {a b} → a <> b → b <> a
<>-sym f<>t = t<>f
<>-sym t<>f = f<>t

≡⊎<> : ∀ a b → a ≡ b ⊎ a <> b
≡⊎<> false false = inj₁ refl
≡⊎<> false true = inj₂ f<>t
≡⊎<> true false = inj₂ t<>f
≡⊎<> true true = inj₁ refl

--
-- Dirichlet's (pigeonhole) principle for 2 holes.
--

dirichlet2 : ∀ {a b} → a <> b → ∀ c → c ≡ a ⊎ c ≡ b
dirichlet2 f<>t false = inj₁ refl
dirichlet2 f<>t true  = inj₂ refl
dirichlet2 t<>f false = inj₂ refl
dirichlet2 t<>f true  = inj₁ refl

-- `T a vs ws` means that vs is obtained from ws by
-- (1) first copying the prefix of words starting with the letter b,
--     where a ≢ b, and
-- (2) then appending the tails of words starting with a.

data T (a : Letter) : (vs ws : List Word) → Set where
  t-init : ∀ {v ws b} → (a<>b : a <> b) →
           T a (v ∷ b ∷∈ ws) ((a ∷ v) ∷ b ∷∈ ws)
  t-keep : ∀ {v vs ws} →
           (t : T a vs ws) → T a (v ∷ vs) ((a ∷ v) ∷ ws)
  t-drop : ∀ {v vs ws b} → (a<>b : a <> b) →
           (t : T a vs ws) → T a vs ((b ∷ v) ∷ ws)
  t-[]   : T a [] []  -- This rule ensures that `T a ws (a ∷∈ ws)` for all `ws`.

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
t-∋⊴-drop (t-init a<>b) (here ⊴v) = here (⊴-keep ⊴v)
t-∋⊴-drop (t-init a<>b) (there ∋⊴v) = there (∋⊴-drop ∋⊴v)
t-∋⊴-drop (t-keep t) (here ⊴v) = here (⊴-keep ⊴v)
t-∋⊴-drop (t-keep t) (there ∋⊴v) = there (t-∋⊴-drop t ∋⊴v)
t-∋⊴-drop (t-drop a<>b t) ∋⊴v = there (t-∋⊴-drop t ∋⊴v)
t-∋⊴-drop t-[] ()

-- Lemmas. Good ... → Good ...

good-∷∈ : ∀ {a ws} → Good ws → Good (a ∷∈ ws)
good-∷∈ (here ws∋⊴w) = here (∋⊴-∷∈ ws∋⊴w)
good-∷∈ (there good-ws) = there (good-∷∈ good-ws)

t-good : ∀ {a vs ws} → T a vs ws → Good vs → Good ws
t-good (t-init a<>b) (here b-ws∋⊴v) = here (∋⊴-drop b-ws∋⊴v)
t-good (t-init a<>b) (there good-b-vs) = there good-b-vs
t-good (t-keep t) (here vs∋⊴v) = here (t-∋⊴-drop t vs∋⊴v)
t-good (t-keep t) (there good-vs) = there (t-good t good-vs)
t-good (t-drop a<>b t) good-vs = there (t-good t good-vs)
t-good t-[] ()

-- Lemma. T a (...) (a ∷∈ ...)

t-∷∈ : ∀ a vs → T a vs (a ∷∈ vs)
t-∷∈ a [] = t-[]
t-∷∈ a (x ∷ xs) = t-keep (t-∷∈ a xs)

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
-- then case distinction on first letter of first word following zs

mutual

  ttBar : ∀ {zs a b xs ys} → a <> b → T a xs zs → T b ys zs →
            Bar xs → Bar ys → Bar zs
  ttBar a<>b ta tb (now nx) bar-ys = now (t-good ta nx)
  ttBar a<>b ta tb (later lx) bar-ys = ttBar₁ a<>b ta tb lx bar-ys

  ttBar₁ : ∀ {zs a b xs ys} → a <> b → T a xs zs → T b ys zs →
             (∀ w → Bar (w ∷ xs)) → Bar ys → Bar zs
  ttBar₁ a<>b ta tb lx (now nx) = now (t-good tb nx)
  ttBar₁ a<>b ta tb lx (later ly) = later (ttBar₂ a<>b ta tb lx ly)

  ttBar₂ : ∀ {zs a b xs ys} → a <> b → T a xs zs → T b ys zs →
             (∀ w → Bar (w ∷ xs)) → (∀ w → Bar (w ∷ ys)) →
             (∀ w → Bar (w ∷ zs))
  ttBar₂ {zs} a<>b ta tb lx ly [] = bar-[]∷ zs
  ttBar₂ {zs}  {a} {b} {xs} {ys} a<>b ta tb lx ly (c ∷ v) with dirichlet2 a<>b c
  ... | inj₁ c≡a rewrite c≡a =
    Bar ((a ∷ v) ∷ zs) ∋
    ttBar a<>b ta′ tb′ (lx v) (later ly)
    where ta′ : T a (v ∷ xs) ((a ∷ v) ∷ zs)
          ta′ = t-keep ta
          tb′ : T b ys ((a ∷ v) ∷ zs)
          tb′ = t-drop (<>-sym $ a<>b) tb
  ... | inj₂ c≡b rewrite c≡b =
    Bar ((b ∷ v) ∷ zs) ∋
    ttBar₁ a<>b ta′ tb′ lx (ly v)
    where ta′ : T a xs ((b ∷ v) ∷ zs)
          ta′ = t-drop a<>b ta
          tb′ : T b (v ∷ ys) ((b ∷ v) ∷ zs)
          tb′ = t-keep tb


--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar ws, then induction on first word following ws


mutual

  bar-∷∈ : ∀ {a ws} → Bar ws → Bar (a ∷∈ ws)
  bar-∷∈ (now n) = now (good-∷∈ n)
  bar-∷∈ (later l) = later (bar-∷∈₁ l)

  bar-∷∈₁ : ∀ {a ws} → (∀ w → Bar (w ∷ ws)) → (∀ w → Bar (w ∷ a ∷∈ ws))
  bar-∷∈₁ {a} {ws} l [] = bar-[]∷ (a ∷∈ ws)
  bar-∷∈₁ {a} {ws} l (b ∷ v) with ≡⊎<> b a
  ... | inj₁ b≡a  rewrite b≡a =
    Bar (a ∷∈ (v ∷ ws)) ∋
    bar-∷∈ (l v)
  ... | inj₂ b<>a =
    Bar ((b ∷ v) ∷ a ∷∈ ws) ∋
    ttBar b<>a tb ta (bar-∷∈₁ l v) (later l)
    where tb : T b (v ∷ a ∷∈ ws) ((b ∷ v) ∷ a ∷∈ ws)
          tb = t-init b<>a
          ta : T a ws ((b ∷ v) ∷ a ∷∈ ws)
          ta = t-drop (<>-sym $ b<>a) (t-∷∈ a ws)

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
