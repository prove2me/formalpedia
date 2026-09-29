-- Prove2me | solution 1 for ECAFixedVariety.rule90_exists_nonzero_fixed_of_three_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:23:38.435923+00:00
-- url     : https://prove2.me/submissions/ce12fe80-4c77-44b3-8319-da2735a7f8c0

-- Sol generated from Novelty/ECAFixedVarietyPeriodThree.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree
import Theorems.Thm_ECAFixedVariety_mem_fixedSet_iff

/-!
# Period-three rigidity: the fixed-point variety depends on `n mod 3`

Wolfram's classification assigns a **single** class to a rule, independently of
the ring size `n`.  We show that the fixed-point variety cannot possibly encode
such an `n`-independent invariant, because for two of the most-studied rules —
the additive Rule 90 and the chaotic Rule 45 (both Wolfram class 3) — the
variety is governed by the arithmetic of `n mod 3`:

* `rule90_period_three`, `rule45_period_three` — every stationary configuration
  of Rule 90 or Rule 45 is invariant under the shift by `3`.
* `rule90_fixedSet_eq_zero_of_not_three_dvd` — if `3 ∤ n` then Rule 90 has only
  the zero configuration: dimension `0`.
* `rule90_exists_nonzero_fixed_of_three_dvd` — if `3 ∣ n` (and `n ≠ 0`) the
  variety is strictly bigger: it contains the `3`-periodic wave `011011…`.
* `rule90_hasFixedDim_le_two` — but it never exceeds dimension `2`; in
  particular `rule90_dim_lt_half`, so a class-3 rule violates the predicted
  `dim ≥ n/2` for all `n ≥ 5`.
* `rule45_fixedSet_empty_of_not_three_dvd` — the class-3 Rule 45 has an
  **empty** fixed-point variety when `3 ∤ n`, so no dimension is even definable.
* `rule45_exists_fixed_of_three_dvd` — while for `3 ∣ n` it is non-empty.

The common mechanism is the *transfer relation* of the fixed-point subshift: for
both rules two (resp. three) consecutive stationarity constraints force
`s_{i+3} = s_i`, and when `3` is invertible in `ZMod n` this collapses the whole
configuration to a constant, which the local rule then pins down.
-/

open ECAFixedVariety

/-! ### Consequences of shift-by-three invariance -/


/-! ### Rule 90 -/










/-! ### Rule 45 -/







open ECAFixedVariety in
theorem solution{n : ℕ} (h : 3 ∣ n) :
    ∃ s ∈ fixedSet 90 n, s ≠ 0 := by
  refine ⟨wave3 h, ?_, ?_⟩
  · rw [mem_fixedSet_iff]
    intro i
    have key : ∀ x : ZMod 3,
        localRuleZ 90 (if x - 1 = 0 then 0 else 1) (if x = 0 then 0 else 1)
          (if x + 1 = 0 then 0 else 1) = (if x = 0 then 0 else 1) := by decide
    have e1 : ZMod.castHom h (ZMod 3) (i - 1) = ZMod.castHom h (ZMod 3) i - 1 := by
      rw [map_sub, map_one]
    have e2 : ZMod.castHom h (ZMod 3) (i + 1) = ZMod.castHom h (ZMod 3) i + 1 := by
      rw [map_add, map_one]
    simp only [wave3, e1, e2]
    exact key _
  · intro hzero
    have h1 : wave3 h 1 = 0 := by rw [hzero]; rfl
    rw [wave3] at h1
    simp only [map_one] at h1
    revert h1
    norm_num
