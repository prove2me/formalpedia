-- Prove2me | Theorems.Thm_ECAFixedVariety_rule45_exists_fixed_of_three_dvd
-- name    : ECAFixedVariety.rule45_exists_fixed_of_three_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:33:34.028927+00:00
-- url     : https://prove2.me/theorems/1f84aac2-c8d3-4372-a484-4268559be495
-- title:
--   For `3 ∣ n` the Rule 45 variety is non-empty: it contains the pulse
-- statement:
--   **For `3 ∣ n` the Rule 45 variety is non-empty**: it contains the pulse
--   train of period `3`.
--
--   ```lean
--   theorem ECAFixedVariety.rule45_exists_fixed_of_three_dvd{n : ℕ} (h : 3 ∣ n) :
--       pulse3 h ∈ fixedSet 45 n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAFixedVarietyPeriodThree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAFixedVarietyPeriodThree.lean#L204

-- Thm stub generated from Novelty/ECAFixedVarietyPeriodThree.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree

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

theorem ECAFixedVariety.rule45_exists_fixed_of_three_dvd{n : ℕ} (h : 3 ∣ n) :
    pulse3 h ∈ fixedSet 45 n := by sorry
