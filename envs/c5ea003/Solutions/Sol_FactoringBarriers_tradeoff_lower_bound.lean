-- Prove2me | solution 1 for FactoringBarriers.tradeoff_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:37:35.024869+00:00
-- url     : https://prove2.me/submissions/cf7a4308-bc14-41f1-9bff-c77d327d6e66

-- Sol generated from Cryptography/FactoringBarriers/TradeoffBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Theorems.Thm_FactoringBarriers_geom_mean_le_arith_mean_of_card

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
theorem solution{k : ℕ} (hk : 0 < k) (x : ℝ) (y : Fin k → ℝ)
    (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = x) :
    (k : ℝ) * Real.exp (x ^ (1 / (k : ℝ))) ≤ ∑ i, Real.exp (y i) := by
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- Step 1: the balance point dominates the geometric mean of the budgets.
  have h1 : x ^ (1 / (k : ℝ)) ≤ (∑ i, y i) / k := by
    have := geom_mean_le_arith_mean_of_card hk y (fun i => (hy i).le)
    rwa [hprod] at this
  -- Step 2: AM–GM applied to the *costs* `exp (y i)`.
  have h2 : Real.exp ((∑ i, y i) / k) ≤ (∑ i, Real.exp (y i)) / k := by
    have hz : ∀ i, (0:ℝ) ≤ Real.exp (y i) := fun i => (Real.exp_pos _).le
    have := geom_mean_le_arith_mean_of_card hk (fun i => Real.exp (y i)) hz
    have hprodexp : (∏ i, Real.exp (y i)) = Real.exp (∑ i, y i) := by
      rw [Real.exp_sum]
    rw [hprodexp] at this
    have hrw : Real.exp (∑ i, y i) ^ (1 / (k : ℝ)) = Real.exp ((∑ i, y i) / k) := by
      rw [← Real.exp_one_rpow (∑ i, y i), ← Real.rpow_mul (Real.exp_pos 1).le,
        ← Real.exp_one_rpow ((∑ i, y i) / k)]
      congr 1
      field_simp
    rwa [hrw] at this
  have h3 : Real.exp (x ^ (1 / (k : ℝ))) ≤ (∑ i, Real.exp (y i)) / k :=
    le_trans (Real.exp_le_exp.mpr h1) h2
  rw [le_div_iff₀ hkR] at h3
  linarith
