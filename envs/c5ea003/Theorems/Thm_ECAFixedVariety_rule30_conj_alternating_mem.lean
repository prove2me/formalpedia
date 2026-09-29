-- Prove2me | Theorems.Thm_ECAFixedVariety_rule30_conj_alternating_mem
-- name    : ECAFixedVariety.rule30_conj_alternating_mem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:33:19.86167+00:00
-- url     : https://prove2.me/theorems/d2804b3e-a556-4a4e-bfc7-ef8e86efbca6
-- title:
--   Its colour-complement is stationary as well.
-- statement:
--   Its colour-complement is stationary as well.
--
--   ```lean
--   theorem ECAFixedVariety.rule30_conj_alternating_mem{n : ℕ} (h : 2 ∣ n) :
--       conjCfg (alternating h) ∈ fixedSet 30 n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECARule30Chaos.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECARule30Chaos.lean#L120

-- Thm stub generated from Novelty/ECARule30Chaos.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAParityRule150
import Definitions.Def_Novelty_ECASymmetryOrbit

/-!
# Cycle 6: Rule 30, the canonical chaotic automaton, has a three-point locus

Rule 30 is Wolfram's flagship class-3 rule (it was used as a random number
generator).  Its stationarity constraints are

* `s_i = 0 ⟹ s_{i-1} = s_{i+1}`, and
* `s_i = 1 ⟹ s_{i-1} = 0`,

which force spatial period two.  We determine its fixed-point locus completely:

* `rule30_period_two` — every stationary configuration has period `2`.
* `rule30_fixedSet_of_odd` — on an odd ring only the zero configuration is
  stationary.
* `rule30_fixedSet_of_even` — on an even ring the locus is exactly
  `{0, alternating, ¬alternating}`, a **three**-point set.
* `rule30_ncard_of_even`, `rule30_not_affine_of_even`,
  `rule30_no_fixed_dim_of_even` — since `3 ∤ 2ⁿ`, the locus of the canonical
  chaotic rule is not an affine subvariety and has **no dimension**, for
  infinitely many ring sizes at once (not merely in a single computed example).

This upgrades the Lagrange obstruction of Cycle 1 from a finite check to an
infinite family, and it does so for the very rule that the conjecture would
place at `dim ≥ n/2`.
-/

open ECAFixedVariety






/-! ### Even rings: an explicit three-point locus -/

theorem ECAFixedVariety.rule30_conj_alternating_mem{n : ℕ} (h : 2 ∣ n) :
    conjCfg (alternating h) ∈ fixedSet 30 n := by sorry
