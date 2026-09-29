-- Prove2me | solution 1 for QubitTrade.outcomes_subset_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:39:19.306279+00:00
-- url     : https://prove2.me/submissions/afd9498f-0328-459e-971b-fe0cab24e493

-- Sol generated from Algebra/QubitTrade/Capacity.lean
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






/-! ## Divisor ambiguity, at every register size -/




open QubitTrade in
theorem solution{t r r' : ℕ} (hr' : 0 < r') (hdvd : r ∣ r') :
    outcomes t r ⊆ outcomes t r' := by
  obtain ⟨s, rfl⟩ := hdvd
  rintro m ⟨k, hk, rfl⟩
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp at hr'
    · exact hs
  refine ⟨s * k, ?_, ?_⟩
  · calc s * k < s * r := (Nat.mul_lt_mul_left hs).mpr hk
      _ = r * s := mul_comm s r
  · unfold truncOutcome
    rw [show 2 ^ t * (s * k) = (2 ^ t * k) * s by ring, Nat.mul_div_mul_right _ _ hs]
