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
open import Data.List as List
  using (List; []; _∷_; length)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂)

open import Function
  using (_$_; _∋_)

open import Relation.Binary.PropositionalEquality
  renaming([_] to ≡[_])

-- Words are modelled as lists of letters from
-- the two letter alphabet.

data Letter : Set where
  l0 l1 : Letter

Word = List Letter
Seq = List Word

-- The embedding relation on words is defined inductively.
-- Intuitively, a word `v` can be embedded into a word `w`,
-- if we can obtain `v` by deleting letters from `w`.
-- For example,
--   l1 ∷ l0 ∷ l1 ∷ [] ⊴ l0 ∷ l1 ∷ l0 ∷ l0 ∷ l1 ∷ []

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

data Good : (ws : Seq) → Set where
  here  : ∀ {ws w} (ws∋⊴w : ws ∋⊴ w) → Good (w ∷ ws)
  there : ∀ {ws w} (good-ws : Good ws) → Good (w ∷ ws)

-- In order to express the fact that every infinite sequence is good,
-- we define a predicate Bar.
--
-- Intuitively, Bar ws means that either
-- (1) the list of words ws is already good, or
-- (2) successively adding words will turn it into a good list.

mutual

  data Bar : Seq → Set where
    now   : ∀ {ws} (n : Good ws) → Bar ws
    later : ∀ {ws} (l : Later ws) → Bar ws

  Later : Seq → Set
  Later ws = ∀ w → Bar (w ∷ ws)

-- Consequently,
--   Bar []
-- means that every infinite sequence must be good,
-- since by successively adding words to the empty list, we must
-- eventually arrive at a list which is good.

-- (Note that the above definition of Bar is closely related to
-- Brouwer’s more general principle of bar induction.)

-- The following function adds a letter to each word in a word list. 

infixr 5 _∷∈_

_∷∈_ : (a : Letter) (ws : Seq) → Seq
a ∷∈ [] = []
a ∷∈ w ∷ ws = (a ∷ w) ∷ a ∷∈ ws

-- Inequality of letters.

infix 4 _<>_

data _<>_ : (a b : Letter) → Set where
  l0<>l1 : l0 <> l1
  l1<>l0 : l1 <> l0

<>-sym : ∀ {a b} → a <> b → b <> a
<>-sym l0<>l1 = l1<>l0
<>-sym l1<>l0 = l0<>l1

≡⊎<> : ∀ a b → a ≡ b ⊎ a <> b
≡⊎<> l0 l0 = inj₁ refl
≡⊎<> l0 l1 = inj₂ l0<>l1
≡⊎<> l1 l0 = inj₂ l1<>l0
≡⊎<> l1 l1 = inj₁ refl

--
-- Dirichlet's (pigeonhole) principle for 2 holes.
--

dirichlet2 : ∀ {a b} → a <> b → ∀ c → c ≡ a ⊎ c ≡ b
dirichlet2 l0<>l1 l0 = inj₁ refl
dirichlet2 l0<>l1 l1 = inj₂ refl
dirichlet2 l1<>l0 l0 = inj₂ refl
dirichlet2 l1<>l0 l1 = inj₁ refl

-- `T a vs ws` means that vs is obtained from ws by
-- (1) first copying the prefix of words starting with the letter b,
--     where a ≢ b, and
-- (2) then appending the tails of words starting with a.

data T (a : Letter) : (vs ws : Seq) → Set where
  init : ∀ {w ws b} (a<>b : a <> b) →
           T a (w ∷ b ∷∈ ws) ((a ∷ w) ∷ b ∷∈ ws)
  keep : ∀ {w vs ws} →
           T a vs ws → T a (w ∷ vs) ((a ∷ w) ∷ ws)
  drop : ∀ {w vs ws b} (a<>b : a <> b) →
           T a vs ws → T a vs ((b ∷ w) ∷ ws)
  []   : T a [] []  -- This rule ensures that `T a ws (a ∷∈ ws)`.

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

bar[]∷ : (ws : Seq) → Bar ([] ∷ ws)
bar[]∷ ws = later (λ w → now (here (here ([]⊴ w))))

-- Lemmas. w ⊵∃ ... → (a ∷ w) ⊵∃ ...

∋⊴-drop : ∀ {ws a v} → ws ∋⊴ v → ws ∋⊴ a ∷ v
∋⊴-drop (here w⊴v) = here (⊴-drop w⊴v)
∋⊴-drop (there ws∋⊴v) = there (∋⊴-drop ws∋⊴v)

∋⊴-keep : ∀ {ws a v} → ws ∋⊴ v → a ∷∈ ws ∋⊴ a ∷ v
∋⊴-keep (here w⊴v) = here (⊴-keep w⊴v)
∋⊴-keep (there ws∋⊴v) = there (∋⊴-keep ws∋⊴v)

t-∋⊴-drop : ∀ {a v vs ws} → T a vs ws → vs ∋⊴ v → ws ∋⊴ a ∷ v
t-∋⊴-drop (init a<>b) (here ⊴v) = here (⊴-keep ⊴v)
t-∋⊴-drop (init a<>b) (there ∋⊴v) = there (∋⊴-drop ∋⊴v)
t-∋⊴-drop (keep t) (here ⊴v) = here (⊴-keep ⊴v)
t-∋⊴-drop (keep t) (there ∋⊴v) = there (t-∋⊴-drop t ∋⊴v)
t-∋⊴-drop (drop a<>b t) ∋⊴v = there (t-∋⊴-drop t ∋⊴v)

-- Lemmas. Good ... → Good ...

good∷ : ∀ {a ws} → Good ws → Good (a ∷∈ ws)
good∷ (here ws∋⊴w) = here (∋⊴-keep ws∋⊴w)
good∷ (there good-ws) = there (good∷ good-ws)

t-good : ∀ {a vs ws} → T a vs ws → Good vs → Good ws
t-good (init a<>b) (here b-ws∋⊴v) = here (∋⊴-drop b-ws∋⊴v)
t-good (init a<>b) (there good-b-vs) = there good-b-vs
t-good (keep t) (here vs∋⊴v) = here (t-∋⊴-drop t vs∋⊴v)
t-good (keep t) (there good-vs) = there (t-good t good-vs)
t-good (drop a<>b t) good-vs = there (t-good t good-vs)

-- Lemma. T a (...) (a ∷∈ ...)

t∷ : ∀ a ws → T a ws (a ∷∈ ws)
t∷ a [] = []
t∷ a (w ∷ ws) = keep (t∷ a ws)

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
-- then case distinction on first letter of first word following zs

mutual

  tt-bb : ∀ {zs a b xs ys} → a <> b → T a xs zs → T b ys zs →
            Bar xs → Bar ys → Bar zs
  tt-bb a<>b ta tb (now nx) bar-ys = now (t-good ta nx)
  tt-bb a<>b ta tb (later lx) bar-ys = tt-lb a<>b ta tb lx bar-ys

  tt-lb : ∀ {zs a b xs ys} → a <> b → T a xs zs → T b ys zs →
            Later xs → Bar ys → Bar zs
  tt-lb a<>b ta tb lx (now ny) = now (t-good tb ny)
  tt-lb a<>b ta tb lx (later ly) = later (tt-ll a<>b ta tb lx ly)

  tt-ll : ∀ {zs a b xs ys} → a <> b → T a xs zs → T b ys zs →
            Later xs → Later ys → Later zs
  tt-ll {zs} a<>b ta tb lx ly [] = bar[]∷ zs
  tt-ll {zs} {a} {b} {xs} {ys} a<>b ta tb lx ly (c ∷ v)
    with dirichlet2 a<>b c
  ... | inj₁ c≡a rewrite c≡a =
    Bar ((a ∷ v) ∷ zs) ∋
    tt-bb a<>b ta′ tb′ (lx v) (later ly)
    where ta′ : T a (v ∷ xs) ((a ∷ v) ∷ zs)
          ta′ = keep ta
          tb′ : T b ys ((a ∷ v) ∷ zs)
          tb′ = drop (<>-sym a<>b) tb
  ... | inj₂ c≡b rewrite c≡b =
    Bar ((b ∷ v) ∷ zs) ∋
    tt-lb a<>b ta′ tb′ lx (ly v)
    where ta′ : T a xs ((b ∷ v) ∷ zs)
          ta′ = drop a<>b ta
          tb′ : T b (v ∷ ys) ((b ∷ v) ∷ zs)
          tb′ = keep tb


--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar ws, then induction on first word following ws

mutual

  bar∷ : ∀ b ws → Bar ws → Bar (b ∷∈ ws)
  bar∷ b ws (now n) = now (good∷ n)
  bar∷ b ws (later l) = later (bar∷l b ws l)

  bar∷l : ∀ b ws → Later ws → Later (b ∷∈ ws)
  bar∷l b ws l [] = bar[]∷ (b ∷∈ ws)
  bar∷l b ws l (a ∷ w) with ≡⊎<> a b
  ... | inj₁ a≡b rewrite a≡b =
    Bar (b ∷∈ w ∷ ws) ∋
    bar∷ b (w ∷ ws) (l w)
  ... | inj₂ a<>b =
    Bar zs ∋
    tt-bb a<>b t1 t2 b1 b2
    where zs = (a ∷ w) ∷ b ∷∈ ws
          xs = w ∷ b ∷∈ ws
          ys = ws
          t1 : T a xs zs
          t1 = init a<>b
          b1 : Bar xs
          b1 = bar∷l b ws l w
          t2 : T b ws zs
          t2 = drop (<>-sym a<>b) (t∷ b ws)
          b2 : Bar ws
          b2 = later l

--
-- higman: Main theorem
--

higman′ :  Later []
higman′ [] = bar[]∷ []
higman′ (c ∷ cs) = bar∷ c (cs ∷ []) (higman′ cs)

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
