-- Prove2me | Definitions.Def_Applications_SocialChoice_IncoherenceStratification
-- name    : Applications_SocialChoice_IncoherenceStratification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:59.870348+00:00
-- url     : https://prove2.me/theorems/8dff3b78-13f3-4540-b93d-852f07f66568
-- title:
--   Aether Catalog definitions — Applications_SocialChoice_IncoherenceStratification
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SocialChoice.IncoherenceStratification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SocialChoice/IncoherenceStratification.lean by skeleton subtraction
import Mathlib
/-
# The fragment hierarchy never collapses: stratifying coherence by the index

A companion to `NonFiniteAxiomatization.lean`.  Where that file shows *some*
finite fragment fails, this file pinpoints *why*: the width-`B` fragment passes a
frame exactly when the frame's incoherence index exceeds `B`
(`coherentUpTo_iff_lt_incoherenceIndex`).  Consequently the fragments form a
*strictly* refining chain — for every `B` there is a maximal frame separating
width `B` from width `B+1` (`fragment_strictly_refines`) — so the hierarchy of
finite approximations never stabilizes.

The shared model (frames in `ZMod n`, balanced sequences, incoherence index) and
the three base lemmas about the single-generator frame are reproduced from the
catalog file `IncoherenceIndex.lean`; the monorepo build configuration prevents
importing it in isolation, so the infrastructure is inlined and the **new
results below are the stratification theorems**.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Conjecture: the bounded fragments `CoherentUpTo B`
are governed *exactly* by the incoherence index — `CoherentUpTo B F ↔
B < incoherenceIndex F` for any incoherent frame — so increasing the width by one
strictly increases the discriminating power, and no finite width is terminal.

EXPERIMENT (Experimenter).  Identify `∃ l, IsBalanced F l ∧ l.length ≤ B` with
`∃ k ∈ balancedLengths F, k ≤ B`, and use that `incoherenceIndex = sInf
(balancedLengths F)` is attained (`Nat.sInf_mem`) when the set is non-empty.  The
single-generator frame `{1} ⊆ ZMod (B+1)` has index `B+1`, hence passes width `B`
but fails width `B+1` (the sequence `1` repeated `B+1` times), giving the strict
separator.

ANALYSIS (Analyst).  True and provable.  The index is the *exact* threshold: a
frame survives the width-`B` test iff its shortest violation is longer than `B`.
The strict-refinement corollary is then immediate from realizing index `B+1`.

CRITIQUE (Critic).  The iff is proved by antisymmetric `Nat.sInf` reasoning (not
`decide`); the non-emptiness hypothesis `hne` is essential and explicit (a fully
coherent frame has index `0` yet passes every fragment, so the iff genuinely
needs an actual violation to exist).  `fragment_strictly_refines` exhibits a
concrete maximal witness, so nothing is vacuous.

SYNTHESIS (PI).  Combined with `coherence_not_finitely_axiomatizable`, the index
is revealed as the complete invariant controlling the finite fragments: the
fragments refine strictly and forever, which is the structural reason measurable
majorities admit no bounded finite axiomatization.  See `FUTURE_DIRECTIONS.md`.
-- !-- Lab Notes -- !--
-/

namespace SocialChoice

open scoped BigOperators

/-! ## Catalog model (reproduced from `IncoherenceIndex.lean`) -/

/-- A *standard social decision frame* on `n` social states. -/
abbrev Frame (n : ℕ) := Finset (ZMod n)

/-- A *perfectly balanced sequence* for a frame `F`. -/
def IsBalanced {n : ℕ} (F : Frame n) (l : List (ZMod n)) : Prop :=
  l ≠ [] ∧ (∀ x ∈ l, x ∈ F) ∧ l.sum = 0

/-- The set of lengths of perfectly balanced sequences of `F`. -/
def balancedLengths {n : ℕ} (F : Frame n) : Set ℕ :=
  { k | ∃ l, IsBalanced F l ∧ l.length = k }

/-- The *incoherence index*: the length of the shortest perfectly balanced
sequence. -/
noncomputable def incoherenceIndex {n : ℕ} (F : Frame n) : ℕ :=
  sInf (balancedLengths F)

/-- A frame is *maximal* when its atoms generate the whole decision space. -/
def IsMaximal {n : ℕ} (F : Frame n) : Prop :=
  AddSubgroup.closure (F : Set (ZMod n)) = ⊤

/-- The *width-`B` finite fragment*: a frame passes it when it admits no perfectly
balanced sequence of length `≤ B`. -/
def CoherentUpTo {n : ℕ} (B : ℕ) (F : Frame n) : Prop :=
  ¬ ∃ l, IsBalanced F l ∧ l.length ≤ B




/-! ## New results: the index is the exact fragment threshold -/

/-
**Exact threshold.** For a frame that admits at least one perfectly balanced
sequence (an *incoherent* frame), the width-`B` fragment is passed precisely when
the incoherence index strictly exceeds `B`.  Thus the index is the exact length
at which the bounded fragments begin to detect the incoherence.
-/

/-
**Strict refinement.** For every `B` there is a *maximal* standard frame that
passes the width-`B` fragment but fails the width-`(B+1)` fragment.  Hence each
successive fragment is strictly stronger and the hierarchy never collapses.
-/

end SocialChoice


