-- Prove2me | Theorems.Thm_SocialChoice_incoherenceIndex_singleton
-- name    : SocialChoice.incoherenceIndex_singleton
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:03:10.484962+00:00
-- url     : https://prove2.me/theorems/87989c84-18c0-4ff1-9a3d-0bf0a72bb7f5
-- title:
--   IncoherenceIndex singleton
-- statement:
--   Formal statement of `SocialChoice.incoherenceIndex_singleton` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SocialChoice.incoherenceIndex_singleton{n : ℕ} [NeZero n] (a : ZMod n) :
--       incoherenceIndex ({a} : Frame n) = addOrderOf a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/SocialChoice/OrderSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/SocialChoice/OrderSpectrum.lean#L115

-- Thm stub generated from Applications/SocialChoice/OrderSpectrum.lean
import Mathlib
import Definitions.Def_Applications_SocialChoice_OrderSpectrum
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

open SocialChoice

open scoped BigOperators

/-! ## Catalog model (reproduced from `IncoherenceIndex.lean`) -/







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

theorem SocialChoice.incoherenceIndex_singleton{n : ℕ} [NeZero n] (a : ZMod n) :
    incoherenceIndex ({a} : Frame n) = addOrderOf a := by sorry
