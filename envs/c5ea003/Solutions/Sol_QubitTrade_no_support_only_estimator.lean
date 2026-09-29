-- Prove2me | solution 1 for QubitTrade.no_support_only_estimator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:48:13.872228+00:00
-- url     : https://prove2.me/submissions/920d123d-8504-40da-bc35-72bbc289069b

-- Sol generated from Algebra/QubitTrade/Capacity.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Capacity
import Definitions.Def_Algebra_QubitTrade_SupportCollapse
import Theorems.Thm_QubitTrade_outcomes_subset_of_dvd

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
theorem solution{t r s : ℕ} (hr : 0 < r) (hs : 1 < s)
    (A : List ℕ → ℕ) :
    ¬ ((∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t r) → A L = r) ∧
       (∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t (r * s)) → A L = r * s)) := by
  rintro ⟨hA, hA'⟩
  have hsub : outcomes t r ⊆ outcomes t (r * s) :=
    outcomes_subset_of_dvd (Nat.mul_pos hr (by omega)) ⟨s, rfl⟩
  set L : List ℕ := [truncOutcome t r 0] with hL
  have hLr : ∀ m ∈ L, m ∈ outcomes t r := by
    intro m hm
    simp only [hL, List.mem_singleton] at hm
    subst hm
    exact ⟨0, hr, rfl⟩
  have hLr' : ∀ m ∈ L, m ∈ outcomes t (r * s) := fun m hm => hsub (hLr m hm)
  have h1 := hA L hLr
  have h2 := hA' L hLr'
  have : r = r * s := h1.symm.trans h2
  nlinarith
