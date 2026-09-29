-- Prove2me | solution 1 for FactoringBarriers.tradeoff_unbounded_arity_is_poly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:37:35.593176+00:00
-- url     : https://prove2.me/submissions/64fa183b-10fc-4a49-abf6-472379765ce2

-- Sol generated from Cryptography/FactoringBarriers/TradeoffBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder

/-!
# Why the Exponents Are `1/2` and `1/3`: The Multiplicative Trade-off Barrier

The subexponential factoring algorithms all have running times of the shape
`L[1/k, c]`, with `k = 2` for CFRAC / quadratic sieve / ECM and `k = 3` for the
number field sieve.  This file isolates the *structural* reason, as a theorem
about the shape of the cost function rather than a fact about any particular
algorithm.

**Model.** A `k`-way trade-off strategy splits the work into `k` exponential
stages of costs `exp (y 0), …, exp (y (k-1))`, where the "budget" parameters
`y i` are subject to a *multiplicative* constraint `∏ i, y i = x`
(`x = log N`): making one stage cheaper makes another proportionally more
expensive.  Sieving is the canonical example: the smoothness bound and the
relation-collection effort trade off multiplicatively in `log N`.

**Main results.**

* `tradeoff_lower_bound` — every `k`-way trade-off costs at least
  `k · exp (x^{1/k})`; the exponent `1/k` is forced by AM–GM, not chosen.
* `tradeoff_attained` — the bound is exactly attained at the balanced point
  `y i = x^{1/k}`, so it is sharp and the model is not an over-estimate.
* `tradeoff_cost_superpoly` — for each *fixed* `k`, `k · exp (x^{1/k})` is
  superpolynomial: no fixed-arity trade-off strategy can run in polynomial time.
* `tradeoff_unbounded_arity_is_poly` — and here is the honest boundary: if the
  arity `k` may grow with the input, the same expression drops to
  `O(log N)`.  A `k`-way trade-off barrier is therefore a statement about
  *bounded* arity; escaping it requires unboundedly many balanced stages,
  which is precisely the structural novelty no classical method supplies.
-/

open FactoringBarriers

open Filter Finset Real
open scoped Topology

/-! ## AM–GM in the two forms we need -/


/-! ## The trade-off lower bound -/



/-! ## Fixed arity cannot reach polynomial time -/




/-! ## The honest boundary: unbounded arity destroys the barrier -/



open FactoringBarriers in
theorem solution{x : ℝ} (hx : Real.exp 1 < x) :
    ∃ k : ℕ, 0 < k ∧
      (k : ℝ) * Real.exp (x ^ (1 / (k : ℝ))) ≤ Real.exp (Real.exp 1) * (Real.log x + 1) := by
  have hx0 : (0:ℝ) < x := lt_trans (Real.exp_pos 1) hx
  have hlog1 : (1:ℝ) < Real.log x := by
    have := Real.log_lt_log (Real.exp_pos 1) hx
    simpa using this
  refine ⟨⌈Real.log x⌉₊, Nat.ceil_pos.mpr (by linarith), ?_⟩
  set k : ℕ := ⌈Real.log x⌉₊ with hk
  have hkge : Real.log x ≤ (k : ℝ) := Nat.le_ceil _
  have hkR : (0:ℝ) < (k : ℝ) := lt_of_lt_of_le (by linarith) hkge
  have hkle : (k : ℝ) ≤ Real.log x + 1 := by
    have := Nat.ceil_lt_add_one (le_of_lt (by linarith : (0:ℝ) < Real.log x))
    linarith
  -- the balanced budget is at most `e`
  have hxk : x ^ (1 / (k : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_one hkR]
    exact hkge
  calc (k : ℝ) * Real.exp (x ^ (1 / (k : ℝ)))
      ≤ (k : ℝ) * Real.exp (Real.exp 1) := by
        have := Real.exp_le_exp.mpr hxk
        nlinarith [Real.exp_pos (x ^ (1 / (k : ℝ)))]
    _ ≤ (Real.log x + 1) * Real.exp (Real.exp 1) := by
        nlinarith [Real.exp_pos (Real.exp 1)]
    _ = Real.exp (Real.exp 1) * (Real.log x + 1) := by ring
