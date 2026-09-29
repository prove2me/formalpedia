-- Prove2me | Theorems.Thm_mme_dwz_q5_fourth_boundary_original_profile_endpoints
-- name    : mme_dwz_q5_fourth_boundary_original_profile_endpoints
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T18:01:05.218758+00:00
-- url     : https://prove2.me/theorems/e361b6c4-7dfc-429f-9fe3-d217db0e7e2f
-- title:
--   The 24 q=5 fourth boundary endpoints at original profiles and ledger rates
-- statement:
--   For every field K and each of the 24 supported q=5 fourth-level boundary addresses (at least one of i,j,k is zero), prove the canonical constituent prescribed-Z six-symmetrized restriction value at the original rawProfile and the exact componentLogFloor from the ledger, at tau=790643/1000000. ComponentEndpoint fixes all tensor, basis, grading, profile and rate data. These are precisely the boundary inputs needed by the concrete global 2401.01 assembly. The input profile must be preserved, including for k=0.
-- source:
--   Duan-Wu-Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (25), Equation (34), Section 7.3, Table 3; https://arxiv.org/abs/2210.10173v5. Original prescribed profiles and exact component row floors from the revised q=5 fourth-power ledger.

import Definitions.Def_mme_dwz_q5_global_component_ledger_data
universe u
set_option autoImplicit false

theorem mme_dwz_q5_fourth_boundary_original_profile_endpoints {K : Type u} [Field K]
    (c : Fin 45) (hc : ∃ i : Fin 3, MME.DWZFourthGlobalWitness.coarseAddress c i = 0) :
    MME.DWZQ5GlobalLedger.ComponentEndpoint K c := by sorry
