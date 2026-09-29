-- Prove2me | Definitions.Def_Novelty_ECAParityRule150
-- name    : Novelty_ECAParityRule150
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:17:58.549318+00:00
-- url     : https://prove2.me/theorems/58170299-f860-4ae7-a59a-219c85df2232
-- title:
--   Aether Catalog definitions — Novelty_ECAParityRule150
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ECAParityRule150`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ECAParityRule150.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree

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

namespace ECAFixedVariety






/-- The alternating configuration, i.e. the reduction map `ZMod n → ZMod 2`,
available when `n` is even. -/
def alternating {n : ℕ} (h : 2 ∣ n) : Cfg n := fun i => ZMod.castHom h (ZMod 2) i







end ECAFixedVariety


