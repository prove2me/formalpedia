-- Prove2me | solution 1 for ECAFixedVariety.rule30_conj_alternating_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:15:36.698631+00:00
-- url     : https://prove2.me/submissions/ed3f59db-681d-4601-9973-0f7b8ae903f3

-- Sol generated from Novelty/ECARule30Chaos.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAParityRule150
import Definitions.Def_Novelty_ECASymmetryOrbit
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff

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













open ECAFixedVariety in
theorem solution{n : ℕ} (h : 2 ∣ n) :
    conjCfg (alternating h) ∈ fixedSet 30 n := by
  rw [mem_fixedSet_iff]
  intro i
  have e1 : ZMod.castHom h (ZMod 2) (i - 1) = ZMod.castHom h (ZMod 2) i - 1 := by
    rw [map_sub, map_one]
  have e2 : ZMod.castHom h (ZMod 2) (i + 1) = ZMod.castHom h (ZMod 2) i + 1 := by
    rw [map_add, map_one]
  have key : ∀ x : ZMod 2,
      localRuleZ 30 (1 + (x - 1)) (1 + x) (1 + (x + 1)) = 1 + x := by decide
  show localRuleZ 30 (1 + alternating h (i - 1)) (1 + alternating h i)
    (1 + alternating h (i + 1)) = 1 + alternating h i
  simp only [alternating, e1, e2]
  exact key _
