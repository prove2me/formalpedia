-- Prove2me | Definitions.Def_Applications_SocialChoice_OrderSpectrum
-- name    : Applications_SocialChoice_OrderSpectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:03.230198+00:00
-- url     : https://prove2.me/theorems/c8ca4034-4fa1-4ccd-aca8-bd0e2583bf2f
-- title:
--   Aether Catalog definitions — Applications_SocialChoice_OrderSpectrum
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SocialChoice.OrderSpectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SocialChoice/OrderSpectrum.lean by skeleton subtraction
import Mathlib
/-
# The incoherence index is an arithmetic invariant: order formula and spectrum

A companion to `IncoherenceIndex.lean` / `NonFiniteAxiomatization.lean`.  Those
files compute the incoherence index of the *single-generator* frame `{1} ⊆ ZMod n`
(it equals `n`) and use it to prove non-finite-axiomatization.  This file isolates
the **arithmetic mechanism** behind those computations and pushes it to its
natural generality, answering the open question raised in `SaturationContrast.lean`
("classify the index as a function of the atom set"):

* `incoherenceIndex_singleton` — the index of *any* singleton frame `{a} ⊆ ZMod n`
  is exactly the additive order `addOrderOf a` of its generator.  (The catalog's
  `incoherenceIndex_singleton_one` is the special case `a = 1`, recovered below as
  `incoherenceIndex_singleton_one'`.)
* `incoherenceIndex_antitone` — adding atoms can only *shorten* the shortest
  violation: `F ⊆ G` (and `F` incoherent) implies `incoherenceIndex G ≤
  incoherenceIndex F`.  This is the structural law behind the saturation contrast.
* `every_index_realized_maximal` — **every** integer `d ≥ 2` (not just the even
  ones) is the incoherence index of some maximal frame, strengthening the
  catalog's even-only realization.
* `divisor_index_realized` — on a *fixed* `ZMod n`, every divisor `d ≥ 2` of `n`
  is realized as a singleton index.
* `incoherenceIndex_oneTwo_zmod5` — the multi-atom frame `{1,2} ⊆ ZMod 5` has
  index `3`, a value that does **not** divide `5`: multi-generator frames escape
  the divisor lattice that singletons are confined to.

The shared model (frames in `ZMod n`, balanced sequences, incoherence index) and
two base lemmas about the single-generator frame are reproduced from the catalog
file `IncoherenceIndex.lean` (the monorepo build configuration prevents importing
it in isolation, as noted in the sibling files); the **new results are the order
formula, the monotonicity law, and the spectrum theorems below**.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Bold conjecture: the incoherence index is not an ad
hoc count but the *additive order* of the generating data.  For a singleton it
should equal `addOrderOf a`; for several atoms it should be the minimal zero-sum
length over the generated subsemigroup, hence monotone-decreasing in the atom set
and capable of realizing values outside the divisor lattice of `n`.

EXPERIMENT (Experimenter).  Every balanced sequence of `{a}` is `a` repeated `m`
times, with sum `m • a`; `addOrderOf_dvd_iff_nsmul_eq_zero` turns "balanced" into
"`addOrderOf a ∣ m`", whose least positive solution is `addOrderOf a`.  For
monotonicity, `balancedLengths F ⊆ balancedLengths G` and `Nat.sInf` is antitone
on nonempty sets.  Computationally `{1,2} ⊆ ZMod 5` realizes index `3` (`[1,2,2]`
sums to `5 ≡ 0`), confirming the escape from divisors of `5`.

ANALYSIS (Analyst).  True and provable.  Structural pattern: singletons see only
divisors of `n` (Lagrange: `addOrderOf a ∣ n`), while adding atoms both lowers the
index (`antitone`) and unlocks non-divisor values.  The order formula subsumes the
catalog's `{1}` computation and upgrades realization from "even `≥ 4`" to "every
`d ≥ 2`".

CRITIQUE (Critic).  Guards: `incoherenceIndex_singleton` is proved by `sInf`
antisymmetry (no `decide` on the index); `incoherenceIndex_antitone` carries an
explicit nonemptiness hypothesis (a coherent frame has index `0`, which would
break the inequality); `incoherenceIndex_oneTwo_zmod5` proves the lower bound `≥ 3`
by genuinely excluding length-`1` and length-`2` violations, not by `rfl`.

SYNTHESIS (PI).  The incoherence index is exactly the additive order of the atom
data; this single fact regenerates the catalog's realization and unboundedness
results and classifies the realizable spectrum (every `d ≥ 2`, with singletons
confined to divisors).  See `FUTURE_DIRECTIONS.md`.
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


/-! ## The order formula for singleton frames -/

/-
Every list whose entries all lie in the singleton frame `{a}` is `a` repeated.
-/

/-
**Order formula.** The incoherence index of the singleton frame `{a} ⊆ ZMod n`
equals the additive order `addOrderOf a` of its generator.  Every balanced sequence
is `a` repeated `m` times, with sum `m • a`, which vanishes exactly when
`addOrderOf a ∣ m`; the least positive such `m` is `addOrderOf a`.
-/


/-! ## Monotonicity of the index in the atom set -/

/-
Balanced sequences only multiply when atoms are added.
-/

/-
**Saturation law.** Adding atoms can only shorten the shortest coherence
violation: if `F ⊆ G` and `F` is incoherent (admits a balanced sequence), then the
incoherence index of `G` is at most that of `F`.  This is the structural reason the
saturated frame `{1,3} ⊆ ZMod 4` has a smaller index than the sparse `{1}`.
-/

/-! ## Realizing the spectrum -/


/-
**Divisor realization (singleton spectrum).** On a fixed space `ZMod n`, every
divisor `d` of `n` is realized as the incoherence index of a singleton frame,
namely `{↑(n/d)}`.  Combined with Lagrange (`addOrderOf a ∣ n`), this shows the
set of singleton incoherence indices on `ZMod n` is *exactly* the set of divisors
of `n`.
-/

/-! ## Escaping the divisor lattice -/

/-
The two-atom frame `{1,2} ⊆ ZMod 5` admits the balanced sequence `[1,2,2]`.
-/

/-
**Non-divisor index.** The multi-atom frame `{1,2} ⊆ ZMod 5` has incoherence
index `3`.  Since `3 ∤ 5`, multi-generator frames realize indices outside the
divisor lattice to which singleton frames are confined (singleton indices divide
`n` by Lagrange).  Concrete companion to the saturation contrast.
-/

end SocialChoice


