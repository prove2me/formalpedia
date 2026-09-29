-- Prove2me | solution 1 for QubitTrade.samples_do_not_help
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:54:28.429154+00:00
-- url     : https://prove2.me/submissions/9f03cd5c-3e9d-47f2-8247-31ef017427e3

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

/-- **Records coincide.**  Any list of samples observable at order `r` is
observable at order `r'`, whenever both orders exceed the register resolution. -/
theorem outcome_lists_coincide {t r r' : ℕ} (h : 2 ^ t ≤ r) (h' : 2 ^ t ≤ r')
    (L : List ℕ) :
    (∀ m ∈ L, m ∈ outcomes t r) ↔ (∀ m ∈ L, m ∈ outcomes t r') := by
  constructor <;> intro hL m hm
  · rw [outcomes_eq_alphabet h'] at *
    have := hL m hm
    rwa [outcomes_eq_alphabet h] at this
  · rw [outcomes_eq_alphabet h] at *
    have := hL m hm
    rwa [outcomes_eq_alphabet h'] at this







open QubitTrade in
theorem solution{t r r' : ℕ} (h : 2 ^ t ≤ r) (h' : 2 ^ t ≤ r')
    (hne : r ≠ r') (A : List ℕ → ℕ) :
    ¬ ((∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t r) → A L = r) ∧
       (∀ L : List ℕ, (∀ m ∈ L, m ∈ outcomes t r') → A L = r')) := by
  rintro ⟨hA, hA'⟩
  -- a record of any length made of genuine samples of *both* orders
  obtain ⟨k, hk, hk0⟩ := truncOutcome_surjective h (m := 0) (Nat.two_pow_pos t)
  set L : List ℕ := [0] with hL
  have hLr : ∀ m ∈ L, m ∈ outcomes t r := by
    intro m hm
    simp only [hL, List.mem_singleton] at hm
    subst hm
    exact ⟨k, hk, hk0⟩
  have hLr' : ∀ m ∈ L, m ∈ outcomes t r' := (outcome_lists_coincide h h' L).mp hLr
  exact hne ((hA L hLr).symm.trans (hA' L hLr'))
