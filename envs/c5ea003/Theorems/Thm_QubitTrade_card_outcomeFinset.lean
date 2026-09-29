-- Prove2me | Theorems.Thm_QubitTrade_card_outcomeFinset
-- name    : QubitTrade.card_outcomeFinset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:51:37.797341+00:00
-- url     : https://prove2.me/theorems/ae446bb6-cc59-4800-a9e0-2e4d07defc87
-- title:
--   Capacity of a truncated register.
-- statement:
--   **Capacity of a truncated register.**  The number of distinct outcomes at
--   order `r` is exactly `min (2^t) r`: the register is saturated below the collapse
--   threshold and faithful above it.
--
--   ```lean
--   theorem QubitTrade.card_outcomeFinset{t r : ℕ} (hr : 0 < r) :
--       (outcomeFinset t r).card = min (2 ^ t) r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/Capacity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/Capacity.lean#L61

-- Thm stub generated from Algebra/QubitTrade/Capacity.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Capacity
import Definitions.Def_Algebra_QubitTrade_SupportCollapse

/-!
# QUBIT-TRADE V: the capacity of a truncated register, and divisor ambiguity

Two sharper facts about the truncated outcome map `k ↦ ⌊2^t k / r⌋`.

## Capacity

`QubitTrade.card_outcomeFinset` computes the exact number of distinct records a
`t`-bit register can emit at order `r`:

  `#{⌊2^t k / r⌋ : k < r} = min (2^t) r`.

Below the collapse threshold (`2^t ≤ r`) the register is saturated and the answer
`2^t` does not depend on `r` at all — one sample carries `min (t, log₂ r)` bits
about the phase, never more.  Above it the map is injective and the register sees
the full order.

## Divisor ambiguity — an obstruction at *every* register size

`QubitTrade.outcomes_subset_of_dvd`: if `r ∣ r'` (and `r' > 0`) then every record achievable at
order `r` is achievable at order `r'`, *for every `t`*, because `k/r = (sk)/(sr)`
exactly.  Consequently (`QubitTrade.no_support_only_estimator`) no estimator that
reads only which outcomes occurred — as opposed to how often — can distinguish
`r` from any proper multiple of it.  This is the support-level shadow of the
`gcd (k, r) > 1` obstruction repaired, statistically, in `SampleFungibility.lean`:
adding qubits never removes it; only the *frequencies* of the samples do.
-/

open QubitTrade

theorem QubitTrade.card_outcomeFinset{t r : ℕ} (hr : 0 < r) :
    (outcomeFinset t r).card = min (2 ^ t) r := by sorry
