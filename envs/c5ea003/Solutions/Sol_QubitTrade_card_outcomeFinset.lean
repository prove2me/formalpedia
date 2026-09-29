-- Prove2me | solution 1 for QubitTrade.card_outcomeFinset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:26:10.859568+00:00
-- url     : https://prove2.me/submissions/9d19e1d8-4e26-461f-97a2-f03853575700

-- Sol generated from Algebra/QubitTrade/Capacity.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Capacity
import Definitions.Def_Algebra_QubitTrade_SupportCollapse
import Theorems.Thm_QubitTrade_truncOutcome_injOn
import Theorems.Thm_QubitTrade_truncOutcome_lt
import Theorems.Thm_QubitTrade_truncOutcome_surjective

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


theorem mem_outcomeFinset {t r m : ℕ} :
    m ∈ outcomeFinset t r ↔ ∃ k < r, truncOutcome t r k = m := by
  simp [outcomeFinset, Finset.mem_image, Finset.mem_range]




/-! ## Divisor ambiguity, at every register size -/




open QubitTrade in
theorem solution{t r : ℕ} (hr : 0 < r) :
    (outcomeFinset t r).card = min (2 ^ t) r := by
  rcases le_or_gt (2 ^ t) r with h | h
  · -- saturated: the image is the whole alphabet
    have himg : outcomeFinset t r = Finset.range (2 ^ t) := by
      ext m
      rw [mem_outcomeFinset, Finset.mem_range]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact truncOutcome_lt hk
      · intro hm
        exact truncOutcome_surjective h hm
    rw [himg, Finset.card_range, min_eq_left h]
  · -- faithful: the map is injective on `range r`
    have hinj : Set.InjOn (truncOutcome t r) (Finset.range r : Finset ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact truncOutcome_injOn (le_of_lt h) hr ha hb hab
    rw [outcomeFinset, Finset.card_image_of_injOn hinj, Finset.card_range,
      min_eq_right (le_of_lt h)]
