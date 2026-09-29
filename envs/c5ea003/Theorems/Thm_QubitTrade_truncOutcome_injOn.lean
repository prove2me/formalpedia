-- Prove2me | Theorems.Thm_QubitTrade_truncOutcome_injOn
-- name    : QubitTrade.truncOutcome_injOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:51:59.322227+00:00
-- url     : https://prove2.me/theorems/56946b95-0d1b-4a8f-a4f7-480f7be5fe93
-- title:
--   Above the collapse threshold the outcome map separates all numerators.
-- statement:
--   Above the collapse threshold the outcome map separates all numerators.
--
--   ```lean
--   theorem QubitTrade.truncOutcome_injOn{t r : ℕ} (h : r ≤ 2 ^ t) (hr : 0 < r) :
--       Set.InjOn (truncOutcome t r) (Set.Iio r) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/Capacity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/Capacity.lean#L40

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

theorem QubitTrade.truncOutcome_injOn{t r : ℕ} (h : r ≤ 2 ^ t) (hr : 0 < r) :
    Set.InjOn (truncOutcome t r) (Set.Iio r) := by sorry
