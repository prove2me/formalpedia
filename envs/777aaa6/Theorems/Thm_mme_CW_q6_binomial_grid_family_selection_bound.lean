-- Prove2me | Theorems.Thm_mme_CW_q6_binomial_grid_family_selection_bound
-- name    : mme_CW_q6_binomial_grid_family_selection_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T02:06:45.063723+00:00
-- url     : https://prove2.me/theorems/7c15994a-4afe-4965-abc0-a0235f789a4f
-- title:
--   Balanced binomial grids have only square-root-sized paired-induced selections
-- statement:
--   For every nonnegative integer $n$, put $B=\binom{2n}{n}$. There is a primary $q=6$ family with parameters $N=G=2n$, $L=0$, one outer fiber, and $H=B^2$ entries, together with a common balanced halving, such that every paired-induced indexed selection of $q$ entries satisfies
--   $$q\leq B=\sqrt{H}.$$
--   Here paired-induced means that every paired-cyclic supported triple among the selected indices has all three indices equal. The bound holds for every selection, without any requirement that it arise from a coloring. This exhibits a square-root limit on diagonal selection in valid common-halving families; it does not bound general tensor restrictions or extraction into larger matrix blocks.
-- source:
--   Cartesian products of all half-size subsets of 2n positions, encoded as balanced binary X words with complementary Y words and constant-two Z words. Paired-inducedness forces injectivity of the left-word label.

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
open MME
set_option autoImplicit false

theorem mme_CW_q6_binomial_grid_family_selection_bound (n : ℕ) :
    ∃ family : CWQ6PrimaryHashFamily (2 * n) 0 (2 * n) 1
        ((2 * n).choose n * (2 * n).choose n),
      ∃ halving : family.CommonBalancedXYHalving,
        ∀ (q : ℕ) (index : Fin q → Fin 1 ×
            Fin ((2 * n).choose n * (2 * n).choose n)),
          (∀ i j k, family.PairedCyclicSupported halving (index i) (index j) (index k) →
            i = j ∧ j = k) → q ≤ (2 * n).choose n := by sorry
