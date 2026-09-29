-- Prove2me | Theorems.Thm_StatisticRealization_residue_err_pos
-- name    : StatisticRealization.residue_err_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:37:23.265038+00:00
-- url     : https://prove2.me/theorems/0f4c43d0-2d8e-42d5-a606-e8f0eabb72e1
-- title:
--   Zero realization, concretely.
-- statement:
--   **Zero realization, concretely.**  For every modulus `L ≠ 0` and every sensor threshold `B`
--   there is a two-point population of semiprimes on which every residue-only policy errs: the
--   residue statistic realizes none of the navigation sensor.
--
--   ```lean
--   theorem StatisticRealization.residue_err_pos(L B : ℕ) (hL : L ≠ 0) :
--       ∃ p q₁ q₂ : ℕ, p.Prime ∧ q₁.Prime ∧ q₂.Prime ∧ (p, q₁) ≠ (p, q₂) ∧
--         ∀ f : ℕ → Bool,
--           0 < err ({(p, q₁), (p, q₂)} : Finset (ℕ × ℕ))
--             (fun x => (x.1 * x.2) % L) (fun x => sensor B x.1 x.2) f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/StatisticRealizationBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/StatisticRealizationBound.lean#L178

-- Thm stub generated from Novelty/StatisticRealizationBound.lean
import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap
import Definitions.Def_Novelty_StatisticRealizationBound

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

open StatisticRealization

open Finset

variable {ι κ : Type*} [DecidableEq κ]














/-! ## The navigation sensor against residue statistics -/

open OracleRealizationGap

theorem StatisticRealization.residue_err_pos(L B : ℕ) (hL : L ≠ 0) :
    ∃ p q₁ q₂ : ℕ, p.Prime ∧ q₁.Prime ∧ q₂.Prime ∧ (p, q₁) ≠ (p, q₂) ∧
      ∀ f : ℕ → Bool,
        0 < err ({(p, q₁), (p, q₂)} : Finset (ℕ × ℕ))
          (fun x => (x.1 * x.2) % L) (fun x => sensor B x.1 x.2) f := by sorry
