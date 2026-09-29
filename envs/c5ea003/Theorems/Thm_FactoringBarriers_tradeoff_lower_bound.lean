-- Prove2me | Theorems.Thm_FactoringBarriers_tradeoff_lower_bound
-- name    : FactoringBarriers.tradeoff_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:32.02081+00:00
-- url     : https://prove2.me/theorems/1e204c02-6312-40eb-a482-6abd88769d20
-- title:
--   Multiplicative trade-off barrier.
-- statement:
--   **Multiplicative trade-off barrier.** If a strategy splits into `k`
--   exponential stages whose budget parameters multiply to `x`, its total cost is at
--   least `k · exp (x^{1/k})`.  The exponent `1/k` is *forced*: it is the AM–GM
--   balance point of the constraint, not a design choice.
--
--   ```lean
--   theorem FactoringBarriers.tradeoff_lower_bound{k : ℕ} (hk : 0 < k) (x : ℝ) (y : Fin k → ℝ)
--       (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = x) :
--       (k : ℝ) * Real.exp (x ^ (1 / (k : ℝ))) ≤ ∑ i, Real.exp (y i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/TradeoffBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/TradeoffBarrier.lean#L59

-- Thm stub generated from Cryptography/FactoringBarriers/TradeoffBarrier.lean
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

theorem FactoringBarriers.tradeoff_lower_bound{k : ℕ} (hk : 0 < k) (x : ℝ) (y : Fin k → ℝ)
    (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = x) :
    (k : ℝ) * Real.exp (x ^ (1 / (k : ℝ))) ≤ ∑ i, Real.exp (y i) := by sorry
