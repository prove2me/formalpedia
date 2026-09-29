-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_mode_fiber_degree
-- name    : mme_CW_q6_type2_cyclic_mode_fiber_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:46:04.681595+00:00
-- url     : https://prove2.me/theorems/c220f285-b3f8-41ff-99e2-391ab8cc8f5d
-- title:
--   Exact mode-fiber degree of the cyclic q=6 type-2 hypergraph
-- statement:
--   For the cyclic product of the three exact q=6 type-2 address orientations with multiplicities $(L,L,G,G)$ and $L+G=N$, every fiber of every one of the three cyclic mode-word maps has exactly $${N\choose G}^{4}{2G\choose G}$$ edges. This is the common hypergraph degree used in the Davie--Stothers Salem--Spencer hashing and pruning argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 3.2, equation (3.6), and Lemma 5.1(i), pp. 359-364.

import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity

open MME

set_option autoImplicit false

noncomputable local instance coupledAddressFintype (N : ℕ) : Fintype (CWQ6CoupledAddress N) := inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))

noncomputable local instance exactAddressFintype (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) := Fintype.ofInjective (fun e ↦ e.1) Subtype.val_injective

noncomputable local instance exactAddressDecidableEq (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) := Classical.decEq _

noncomputable local instance type2EdgeFintype (N L G : ℕ) : Fintype (CWQ6Type2CyclicEdge N L G) := inferInstanceAs (Fintype (CWQ6ExactCoupledAddress N L G × (CWQ6ExactCoupledAddress N L G × CWQ6ExactCoupledAddress N L G)))

noncomputable local instance type2EdgeDecidableEq (N L G : ℕ) : DecidableEq (CWQ6Type2CyclicEdge N L G) := Classical.decEq _

noncomputable local instance type2ModeWordDecidableEq (N : ℕ) : DecidableEq (CWQ6Type2CyclicModeWord N) := Classical.decEq _

theorem mme_CW_q6_type2_cyclic_mode_fiber_degree
    (N L G : ℕ) (hLG : L + G = N)
    (e : CWQ6Type2CyclicEdge N L G) (i : Fin 3) :
    ((Finset.univ : Finset (CWQ6Type2CyclicEdge N L G)).filter
      (fun f ↦ cwQ6Type2CyclicModeWord f i = cwQ6Type2CyclicModeWord e i)).card =
      Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
  sorry
