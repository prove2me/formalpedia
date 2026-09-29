-- Prove2me | Definitions.Def_Novelty_StatisticRealizationBound
-- name    : Novelty_StatisticRealizationBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T13:59:36.886182+00:00
-- url     : https://prove2.me/theorems/0cf1f831-2779-476b-9ed9-d56b67126917
-- title:
--   Aether Catalog definitions — Novelty_StatisticRealizationBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StatisticRealizationBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StatisticRealizationBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap

/-!
# Crediting a sensor to a statistic: the exact realization bound

The round-74 experiment credited a policy with *realizing* an oracle sensor by comparing its
predictions to the sensor on a labelled population, first pooled ("lenient") and then inside
`log N` strata ("strict").  The strict verdict was `0 %` for every `N`-only policy.

This file supplies the exact combinatorial law behind such crediting.  Fix a finite population
`P`, a **statistic** `T : ι → κ` (everything a policy is allowed to read: residues, magnitude
stratum, a menu of probe answers, …) and a Boolean **target** `s : ι → Bool` (the sensor).  A
`T`-measurable policy is a map `f : κ → Bool`, and its error count is `err P T s f`.

## Main results

* `err_ge_irredError` : every `T`-measurable policy makes at least
  `irredError P T s = ∑_classes min(#true, #false)` mistakes;
* `exists_majority_optimal` : the class-wise majority vote attains that value exactly;
* `isLeast_err` : hence `irredError P T s` **is** the minimum error — a measurement, not a bound;
* `two_mul_irredError_of_balanced` : if every `T`-class is balanced (`#true = #false`), the
  minimum error is exactly half the population: the statistic realizes *nothing*, which is the
  exact form of the "strict within-strata crediting `0 %`" verdict;
* `residue_err_pos` : instantiated at the navigation sensor of
  `Novelty.OracleRealizationGap`, every residue-only policy has strictly positive error on an
  explicit two-point semiprime population, for every modulus and every threshold.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "percentage of the oracle peak realized" is not an information-theoretic
primitive; it is a minimum-error functional of the statistic the policy is allowed to read, and
it should have a closed form.

Experiment (Experimenter): `ComputationalEvidence.md` enumerates small populations (`|P| ≤ 8`)
and all `2^|κ|` policies by brute force, checking `min_f err = ∑ minorities` in every case.

Analysis (Analyst): the closed form is the sum of class minorities.  Two extremes explain the
two crediting regimes measured in the lab: statistics whose classes are pure give minimum error
`0` (full realization), and statistics whose classes are balanced give minimum error `|P| / 2`
(zero realization, no matter how the policy is fitted).  The lenient pooled credit sits between
because pooling merges strata whose base rates differ.

Critique (Critic): the bound must be attained, else "0 %" would be an artefact of a weak
argument; `exists_majority_optimal` exhibits the optimal policy explicitly.  The theorem is
stated for arbitrary `κ`, so it applies verbatim to menu-answer vectors, not just residues.
-/

namespace StatisticRealization

open Finset

variable {ι κ : Type*} [DecidableEq κ]

/-- The number of population members on which the `T`-measurable policy `f` disagrees with the
target `s`. -/
def err (P : Finset ι) (T : ι → κ) (s : ι → Bool) (f : κ → Bool) : ℕ :=
  (P.filter fun i => f (T i) ≠ s i).card

/-- The minority count of a Boolean target on a finset. -/
def minority (Q : Finset ι) (s : ι → Bool) : ℕ :=
  min (Q.filter fun i => s i = true).card (Q.filter fun i => s i = false).card

/-- The irreducible error of a statistic: the sum of the class minorities. -/
def irredError (P : Finset ι) (T : ι → κ) (s : ι → Bool) : ℕ :=
  ∑ c ∈ P.image T, minority (P.filter fun i => T i = c) s






/-- The class-wise majority vote. -/
def majority (P : Finset ι) (T : ι → κ) (s : ι → Bool) (c : κ) : Bool :=
  decide (((P.filter fun i => T i = c).filter fun i => s i = false).card ≤
    ((P.filter fun i => T i = c).filter fun i => s i = true).card)





/-! ## The navigation sensor against residue statistics -/

open OracleRealizationGap


end StatisticRealization


