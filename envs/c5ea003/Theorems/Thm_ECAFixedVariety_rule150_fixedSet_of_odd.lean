-- Prove2me | Theorems.Thm_ECAFixedVariety_rule150_fixedSet_of_odd
-- name    : ECAFixedVariety.rule150_fixedSet_of_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:33:51.176791+00:00
-- url     : https://prove2.me/theorems/f6fa6559-7d99-4729-b997-b7de66cad5c8
-- title:
--   Odd rings are rigid.
-- statement:
--   **Odd rings are rigid.**  For odd `n` the only stationary configurations of
--   Rule 150 are the two constants.
--
--   ```lean
--   theorem ECAFixedVariety.rule150_fixedSet_of_odd{n : ℕ} (hn : ¬ (2 ∣ n)) :
--       fixedSet 150 n = {0, 1} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAParityRule150.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAParityRule150.lean#L58

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

theorem ECAFixedVariety.rule150_fixedSet_of_odd{n : ℕ} (hn : ¬ (2 ∣ n)) :
    fixedSet 150 n = {0, 1} := by sorry
