-- Prove2me | Definitions.Def_mme_dwz_q5_global_component_ledger_data
-- name    : mme_dwz_q5_global_component_ledger_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-21T17:39:58.454989+00:00
-- url     : https://prove2.me/theorems/29bbae2d-4540-4333-8ee2-cc6244aec28f
-- title:
--   The 45 original-profile inputs to the q=5 global value assembly
-- statement:
--   The global q=5 fourth-power extraction has 45 component inputs, ordered by the existing `coarseAddress` table. This data selects their indices and exact logarithmic value floors from the revised 181-row scalar ledger. Each endpoint is for the actual fourth-level constituent with its canonical Z basis, left-square grade, original `rawProfile`, and tau = 790643/1000000. The endpoint bundle asserts all 45 of these explicitly specified prescribed-profile values. It contains no global extraction, compatibility, or numerical-surplus hypothesis.
-- source:
--   Duan-Wu-Zhou, arXiv:2210.10173v5, Equation (25) and Table 3; https://arxiv.org/abs/2210.10173v5. The 45 rates are the child rows of global ledger node 180 in mme_dwz_fourth_exact_scalar_recurrence_ledger_ma_data.

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_six_symmetrized_tau_value

open MME MME.StothersFourth MME.DWZRestrictedValue
open MME.CompleteSplit.CWFourth MME.DWZQ5ExactData
open MME.DWZFourthGlobalWitness
universe u
set_option autoImplicit false

namespace MME.DWZQ5GlobalLedger

/-- Indices of the 45 fourth-level components in the released 181-row ledger. -/
def ledgerIndex : Fin 45 → ℕ :=
  ![6, 13, 17, 21, 22, 23, 24, 25, 26, 27, 31, 38, 45, 52, 59, 63, 64, 65, 72, 79, 86, 93, 100, 101, 102, 109, 116, 123, 130, 131, 132, 139, 146, 153, 154, 155, 162, 169, 170, 171, 175, 176, 177, 178, 179]

/-- Exact logarithmic floors of those 45 rows in the re-emitted scalar ledger. -/
def componentLogFloor : Fin 45 → ℚ :=
  ![0, (236855371243 / 100000000000 : ℚ), (3974846666669 / 1000000000000 : ℚ), (4999805328373 / 1000000000000 : ℚ), (337435396329 / 62500000000 : ℚ), (5002431774647 / 1000000000000 : ℚ), (796434674989 / 200000000000 : ℚ), (236855371243 / 100000000000 : ℚ), 0, (236855371243 / 100000000000 : ℚ), (32056585721 / 7812500000 : ℚ), (1364339668593 / 250000000000 : ℚ), (769869971361 / 125000000000 : ℚ), (615953393593 / 100000000000 : ℚ), (682548175351 / 125000000000 : ℚ), (2096791343139 / 500000000000 : ℚ), (236855371243 / 100000000000 : ℚ), (794969333623 / 200000000000 : ℚ), (5457358688867 / 1000000000000 : ℚ), (6404755418211 / 1000000000000 : ℚ), (6676015030321 / 1000000000000 : ℚ), (3202624344287 / 500000000000 : ℚ), (2730192919793 / 500000000000 : ℚ), (1991215276093 / 500000000000 : ℚ), (4999806626113 / 1000000000000 : ℚ), (1539739918853 / 250000000000 : ℚ), (6676023212003 / 1000000000000 : ℚ), (6676023499877 / 1000000000000 : ℚ), (6159531789539 / 1000000000000 : ℚ), (5003137655079 / 1000000000000 : ℚ), (2699483164891 / 500000000000 : ℚ), (6159533826087 / 1000000000000 : ℚ), (3202624804523 / 500000000000 : ℚ), (3079765900131 / 500000000000 : ℚ), (1351259981097 / 250000000000 : ℚ), (5002425490079 / 1000000000000 : ℚ), (2730192631343 / 500000000000 : ℚ), (5460385998309 / 1000000000000 : ℚ), (5003137655079 / 1000000000000 : ℚ), (995547053093 / 250000000000 : ℚ), (2096791354177 / 500000000000 : ℚ), (1991215276093 / 500000000000 : ℚ), (236855371243 / 100000000000 : ℚ), (236855371243 / 100000000000 : ℚ), 0]

/-- The concrete endpoint required by global extraction for one original profile. -/
def ComponentEndpoint (K : Type u) [Field K] (c : Fin 45) : Prop :=
  HasPrescribedZSixRestrictionValueAtLeast
    (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
    (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
    (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) =>
      cwSquarePairGrade 5 a.down.val.1)
    (rawProfile c) (790643 / 1000000) (Real.exp (componentLogFloor c : ℝ))

/-- All component inputs, with no global extraction premise. -/
def AllComponentEndpoints (K : Type u) [Field K] : Prop :=
  ∀ c : Fin 45, ComponentEndpoint K c

end MME.DWZQ5GlobalLedger


