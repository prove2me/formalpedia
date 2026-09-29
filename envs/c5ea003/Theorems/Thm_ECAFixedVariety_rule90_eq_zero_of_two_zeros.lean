-- Prove2me | Theorems.Thm_ECAFixedVariety_rule90_eq_zero_of_two_zeros
-- name    : ECAFixedVariety.rule90_eq_zero_of_two_zeros
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:34:23.910222+00:00
-- url     : https://prove2.me/theorems/50ab3027-74c6-44ba-bc8f-887ee63f17a9
-- title:
--   Two stationary Rule-90 configurations agreeing at cells `0` and `1` agree
-- statement:
--   Two stationary Rule-90 configurations agreeing at cells `0` and `1` agree
--   everywhere: the variety embeds into the plane of "initial conditions".
--
--   ```lean
--   theorem ECAFixedVariety.rule90_eq_zero_of_two_zeros{n : ℕ} [NeZero n] {s : Cfg n}
--       (hs : s ∈ fixedSet 90 n) (h0 : s 0 = 0) (h1 : s 1 = 0) : s = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAFixedVarietyPeriodThree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAFixedVarietyPeriodThree.lean#L125

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

theorem ECAFixedVariety.rule90_eq_zero_of_two_zeros{n : ℕ} [NeZero n] {s : Cfg n}
    (hs : s ∈ fixedSet 90 n) (h0 : s 0 = 0) (h1 : s 1 = 0) : s = 0 := by sorry
