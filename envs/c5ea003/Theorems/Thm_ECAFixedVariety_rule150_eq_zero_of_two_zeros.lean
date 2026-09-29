-- Prove2me | Theorems.Thm_ECAFixedVariety_rule150_eq_zero_of_two_zeros
-- name    : ECAFixedVariety.rule150_eq_zero_of_two_zeros
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:33:05.445109+00:00
-- url     : https://prove2.me/theorems/675b9ee3-4ff8-4436-a23a-435c6f2eaf45
-- title:
--   Rule 150 is seed-rigid: a stationary configuration vanishing at the cells
-- statement:
--   Rule 150 is seed-rigid: a stationary configuration vanishing at the cells
--   `0` and `1` vanishes identically.
--
--   ```lean
--   theorem ECAFixedVariety.rule150_eq_zero_of_two_zeros{n : ℕ} [NeZero n] {s : Cfg n}
--       (hs : s ∈ fixedSet 150 n) (h0 : s 0 = 0) (h1 : s 1 = 0) : s = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAParityRule150.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAParityRule150.lean#L111

-- Thm stub generated from Novelty/ECAParityRule150.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree
import Definitions.Def_Novelty_ECAParityRule150

/-!
# Cycle 5: parity rigidity of Rule 150

Rule 150, `f(l,c,r) = l + c + r`, is the second classical additive automaton and
is placed in Wolfram class 3 (chaotic).  Its fixed-point equations read
`l + r = 0`, i.e. `s_{i-1} = s_{i+1}`: the variety is the space of
**period-two** configurations.  Consequently its dimension is controlled by the
parity of the ring size, and never exceeds `2`:

* `rule150_period_two` — every stationary configuration has spatial period `2`.
* `rule150_fixedSet_of_odd` — for odd `n` the variety is exactly the pair of
  constant configurations `{0, 1}`; so if a dimension exists it equals `1`.
* `rule150_alternating_mem` — for even `n` the alternating configuration
  (the reduction map `ZMod n → ZMod 2`) is a non-constant stationary point, so
  the variety strictly grows.
* `rule150_hasFixedDim_le_two` and `rule150_dim_lt_half` — the dimension is at
  most `2` for every `n`, so this class-3 rule violates the conjectured
  `dim ≥ n/2` for all `n ≥ 5`.

Together with the mod-3 dichotomy of Rules 90 and 45 this exhibits the general
phenomenon: the fixed-point variety of an additive rule is the kernel of a
circulant matrix, and its dimension is a *number-theoretic* function of `n` —
never a Wolfram class.
-/

open ECAFixedVariety

theorem ECAFixedVariety.rule150_eq_zero_of_two_zeros{n : ℕ} [NeZero n] {s : Cfg n}
    (hs : s ∈ fixedSet 150 n) (h0 : s 0 = 0) (h1 : s 1 = 0) : s = 0 := by sorry
