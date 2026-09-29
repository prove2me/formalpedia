-- Prove2me | solution 1 for BanditAlgorithm.mdp_phase_regret_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T04:02:03.963629+00:00
-- url     : https://prove2.me/submissions/c58b881d-b72d-447e-97dc-a37df75d6c1f

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Step 2 of the proof of Theorem 38.6: the per-phase telescoping identity

Inside a phase of UCRL2 the optimistic value function `v_k` and gain `ρ_k`
satisfy the Bellman optimality equation along the realised trajectory
(L&S Eq. 38.18),

  `ρ_k = r_{A_t}(S_t) - v_k(S_t) + ⟨P_{k,A_t}(S_t), v_k⟩`,

and the regret of the phase is rearranged (Eq. 38.20 and the display after it)
into three pieces: a telescoping boundary term, a martingale-difference term,
and the transition-estimation error.  That rearrangement is a pure identity
between finite sums, recorded here.

Writing `V t = v_k(S_t)`, `W t = ⟨P_{A_t}(S_t), v_k⟩` for the *true* kernel and
`Wk t = ⟨P_{k,A_t}(S_t), v_k⟩` for the *optimistic* one, the phase regret is

  `∑_{t<N} (ρ_k - r_t) = (V N - V 0) + ∑_{t<N} (W t - V (t+1)) + ∑_{t<N} (Wk t - W t)`.

The first term is bounded by the span of `v_k`, hence by `D`; the second is a
sum of martingale differences, since `W t` is the conditional expectation of
`V (t+1)` given the past; the third is bounded by Hölder's inequality against
the `ℓ¹` radius of the confidence set.
-/

open Finset

/-- **The per-phase regret decomposition of Step 2** (L&S Eq. 38.18-38.20),
as an identity between finite sums. -/
theorem solution (N : ℕ) (ρ : ℝ) (rr V W Wk : ℕ → ℝ)
    (hbell : ∀ t < N, ρ = rr t - V t + Wk t) :
    ∑ t ∈ Finset.range N, (ρ - rr t)
      = (V N - V 0) + ∑ t ∈ Finset.range N, (W t - V (t + 1))
        + ∑ t ∈ Finset.range N, (Wk t - W t) := by
  have hterm : ∀ t ∈ Finset.range N,
      ρ - rr t = (V (t + 1) - V t) + (W t - V (t + 1)) + (Wk t - W t) := by
    intro t ht
    have := hbell t (Finset.mem_range.mp ht)
    linarith
  calc ∑ t ∈ Finset.range N, (ρ - rr t)
      = ∑ t ∈ Finset.range N,
          ((V (t + 1) - V t) + (W t - V (t + 1)) + (Wk t - W t)) :=
        Finset.sum_congr rfl hterm
    _ = (∑ t ∈ Finset.range N, (V (t + 1) - V t))
          + (∑ t ∈ Finset.range N, (W t - V (t + 1)))
          + ∑ t ∈ Finset.range N, (Wk t - W t) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (V N - V 0) + ∑ t ∈ Finset.range N, (W t - V (t + 1))
          + ∑ t ∈ Finset.range N, (Wk t - W t) := by
        rw [Finset.sum_range_sub V]
