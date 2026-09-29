-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_mode_fiber_degree_of_complete_finset
-- name    : mme_CW_q6_type2_cyclic_mode_fiber_degree_of_complete_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:56:36.888126+00:00
-- url     : https://prove2.me/theorems/94e4829e-c123-4576-a9fe-60944016a5fc
-- title:
--   Exact cyclic q=6 type-2 mode degree in a complete finite enumeration
-- statement:
--   Let $A$ be a complete finite enumeration of the exact q=6 coupled addresses with multiplicities $(L,L,G,G)$ and $L+G=N$. In the cyclic product $A^3$, every fiber of every cyclic mode-word map has exactly $${N\choose G}^{4}{2G\choose G}$$ edges. The explicit complete enumeration avoids imposing a global finiteness instance and gives the common degree used by the Davie--Stothers Salem--Spencer pruning argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 3.2, equation (3.6), and Lemma 5.1(i), pp. 359-364.

import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_mode_fiber_degree_of_complete_finset
    (N L G : ℕ) (hLG : L + G = N)
    [DecidableEq (CWQ6ExactCoupledAddress N L G)]
    [DecidableEq (CWQ6Type2CyclicModeWord N)]
    (A : Finset (CWQ6ExactCoupledAddress N L G))
    (hA : ∀ a, a ∈ A)
    (e : CWQ6Type2CyclicEdge N L G) (i : Fin 3) :
    ((A ×ˢ (A ×ˢ A)).filter
      (fun f ↦ cwQ6Type2CyclicModeWord f i = cwQ6Type2CyclicModeWord e i)).card =
      Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
  sorry
