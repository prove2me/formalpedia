-- Prove2me | Definitions.Def_Algebra_QubitTrade_Capacity
-- name    : Algebra_QubitTrade_Capacity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:58:14.937417+00:00
-- url     : https://prove2.me/theorems/151e95c8-596d-4b8c-a206-3816b4cd340c
-- title:
--   Aether Catalog definitions — Algebra_QubitTrade_Capacity
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QubitTrade.Capacity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QubitTrade/Capacity.lean by skeleton subtraction
import Mathlib
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

namespace QubitTrade

/-- The record alphabet actually realised at order `r`, as a `Finset`. -/
def outcomeFinset (t r : ℕ) : Finset ℕ := (Finset.range r).image (truncOutcome t r)





/-! ## Divisor ambiguity, at every register size -/



end QubitTrade


