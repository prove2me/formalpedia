-- Prove2me | solution 1 for QubitTrade.samples_do_not_help_any_budget
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:58:58.869753+00:00
-- url     : https://prove2.me/submissions/c1873992-eb5b-4b93-823c-54bd65948bd7

-- Sol generated from Algebra/QubitTrade/SupportCollapse.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SupportCollapse
import Theorems.Thm_QubitTrade_truncOutcome_lt
import Theorems.Thm_QubitTrade_truncOutcome_surjective

/-!
# QUBIT-TRADE II: classical collapse of a truncated register

A `t`-bit truncated phase register reports, for an order-`r` Shor sample with
numerator `k`, the integer

  `truncOutcome t r k = ⌊2^t · k / r⌋ = (2^t * k) / r`  (natural division).

This file proves the **collapse** half of the experiment: once `2^t ≤ r`, the
outcome map is *onto* the whole outcome alphabet `{0, …, 2^t - 1}`, so the set of
observable records is `{0, …, 2^t-1}` **independently of `r`**.  Consequently:

* `QubitTrade.truncOutcome_surjective` — surjectivity onto the alphabet;
* `QubitTrade.outcomes_eq_alphabet` — the outcome set does not depend on `r`;
* `QubitTrade.outcome_lists_coincide` — every *record* (list of samples, of any
  length) achievable at order `r` is achievable at order `r'`;
* `QubitTrade.samples_do_not_help` — hence **no** estimator, with **any** number
  of samples, can be correct for two distinct orders `r, r' ≥ 2^t`;
* `QubitTrade.collapse_cardinality` — the collapse is massive: all
  `R - 2^t + 1` orders in `[2^t, R]` share one and the same outcome set.

This is the sample-independent lower bound `t > log₂ r`.  It is strictly weaker
than the resolution threshold `t ≈ 2 log₂ r` of `Resolution.lean`, and the two
together bracket the measured `t_min`.
-/

open QubitTrade






/-- **The observable alphabet does not depend on the order.**  For every order
`r ≥ 2^t` the outcome set is the full `t`-bit alphabet. -/
theorem outcomes_eq_alphabet {t r : ℕ} (h : 2 ^ t ≤ r) :
    outcomes t r = {m | m < 2 ^ t} := by
  ext m
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact truncOutcome_lt hk
  · intro hm
    exact truncOutcome_surjective h hm


/-- Every record over the `t`-bit alphabet is realizable at every order `r ≥ 2^t`. -/
theorem records_realizable {t r : ℕ} (h : 2 ^ t ≤ r) {L : List ℕ} (hL : ∀ m ∈ L, m < 2 ^ t) :
    ∀ m ∈ L, m ∈ outcomes t r := by
  intro m hm
  rw [outcomes_eq_alphabet h]
  exact hL m hm






open QubitTrade in
theorem solution{t r r' : ℕ} (h : 2 ^ t ≤ r) (h' : 2 ^ t ≤ r')
    (hne : r ≠ r') (A : List ℕ → ℕ) (n : ℕ) :
    ∃ L : List ℕ, L.length = n ∧ (∀ m ∈ L, m ∈ outcomes t r) ∧
      (∀ m ∈ L, m ∈ outcomes t r') ∧ (A L ≠ r ∨ A L ≠ r') := by
  refine ⟨List.replicate n 0, List.length_replicate .., ?_, ?_, ?_⟩
  · refine records_realizable h ?_
    intro m hm
    rw [List.eq_of_mem_replicate hm]
    exact Nat.two_pow_pos t
  · refine records_realizable h' ?_
    intro m hm
    rw [List.eq_of_mem_replicate hm]
    exact Nat.two_pow_pos t
  · by_cases hA : A (List.replicate n 0) = r
    · exact Or.inr (by rw [hA]; exact hne)
    · exact Or.inl hA
