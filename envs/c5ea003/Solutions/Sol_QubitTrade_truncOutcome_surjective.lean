-- Prove2me | solution 1 for QubitTrade.truncOutcome_surjective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:21:28.353988+00:00
-- url     : https://prove2.me/submissions/2b3cdc69-dfc0-4d9d-bd49-3a423b25a41f

-- Sol generated from Algebra/QubitTrade/SupportCollapse.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SupportCollapse

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














open QubitTrade in
theorem solution{t r : ℕ} (h : 2 ^ t ≤ r) {m : ℕ} (hm : m < 2 ^ t) :
    ∃ k < r, truncOutcome t r k = m := by
  set D : ℕ := 2 ^ t with hD
  have hDpos : 0 < D := Nat.two_pow_pos t
  have hrpos : 0 < r := lt_of_lt_of_le hDpos h
  obtain ⟨q, s, hs, ha⟩ : ∃ q s, s < D ∧ m * r = D * q + s :=
    ⟨(m * r) / D, (m * r) % D, Nat.mod_lt _ hDpos, (Nat.div_add_mod _ _).symm⟩
  -- the ceiling `k = ⌈m r / D⌉` lands in the window `[m r, m r + r)` because `D ≤ r`
  obtain ⟨k, hk1, hk2⟩ : ∃ k, m * r ≤ D * k ∧ D * k < m * r + r := by
    rcases eq_or_ne s 0 with hs0 | hs0
    · exact ⟨q, by omega, by omega⟩
    · have hmul : D * (q + 1) = D * q + D := by ring
      exact ⟨q + 1, by omega, by omega⟩
  have hkr : k < r := by
    have h5 : (m + 1) * r ≤ D * r := Nat.mul_le_mul_right r hm
    have h6 : (m + 1) * r = m * r + r := by ring
    have : D * k < D * r := by omega
    exact lt_of_mul_lt_mul_left this (Nat.zero_le D)
  refine ⟨k, hkr, ?_⟩
  unfold truncOutcome
  rw [← hD]
  have h1 : m ≤ D * k / r := (Nat.le_div_iff_mul_le hrpos).mpr hk1
  have h2 : D * k / r < m + 1 := by
    refine (Nat.div_lt_iff_lt_mul hrpos).mpr ?_
    have : (m + 1) * r = m * r + r := by ring
    omega
  omega
