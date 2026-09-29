-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_selected_cardinality_budget_counterexample
-- name    : mme_CW_q6_common_halving_selected_cardinality_budget_counterexample
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T02:09:37.862978+00:00
-- url     : https://prove2.me/theorems/0ebcd32c-5f5e-4286-8768-b1a6f3d8e93a
-- title:
--   Common halving does not guarantee the required paired-induced selection budget
-- statement:
--   For every integer $n\geq 10^6$, there is a primary $q=6$ family with $N=G=2n$, $L=0$, one outer fiber, and $H\leq 4^{2n}$ entries, admitting a common balanced halving, such that every paired-induced indexed selection of $q$ entries satisfies
--   $$q^3<H^2\exp\!\left(-200\sqrt{2n+1}\right).$$
--   A selection is paired-induced when every paired-cyclic supported triple among its indices is diagonal. Consequently, a common balanced halving and the stated upper bound on the fiber size do not guarantee a selection meeting the proposed finite-extraction cardinality budget. This counterexample concerns diagonal entry selections; it does not refute extraction by general tensor restrictions or by larger matrix blocks.
-- source:
--   Balanced binomial grid construction, the exponential lower bound 2^n <= binomial(2n,n), and the explicit estimate exp(200 sqrt(2n+1)) < binomial(2n,n) for n >= 10^6.

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
open MME
set_option autoImplicit false

theorem mme_CW_q6_common_halving_selected_cardinality_budget_counterexample
    (n : ℕ) (hn : 1000000 ≤ n) :
    ∃ H : ℕ, H ≤ 4 ^ (2 * n) ∧
      ∃ family : CWQ6PrimaryHashFamily (2 * n) 0 (2 * n) 1 H,
        ∃ halving : family.CommonBalancedXYHalving,
          ∀ (q : ℕ) (index : Fin q → Fin 1 × Fin H),
            (∀ i j k, family.PairedCyclicSupported halving (index i) (index j) (index k) →
              i = j ∧ j = k) →
            (q : ℝ) ^ 3 < (H : ℝ) ^ 2 *
              Real.exp (-200 * Real.sqrt (((2 * n + 1 : ℕ) : ℝ))) := by sorry
