-- Prove2me | solution 1 for mme_released_interior_owner1_cell21_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T11:31:10.291181+00:00
-- url     : https://prove2.me/submissions/88812aed-143d-456e-bcd8-81261b9acf09

import Theorems.Thm_mme_released_interior_owner1_cell21_region0_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region1_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region2_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region3_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region4_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region5_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region0_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region1_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region2_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region3_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region4_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell21_region5_112_weight_rate_bound

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

private abbrev Child := Cell 4 6 (ReleasedInterior.parent 21)
private def slot (c : ReleasedInterior.Split 21) : ℕ := 25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val
private def q (c : Child) : ℚ :=
  (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1292781691400863492800000000000000000, 0, 0, 0, 241342744400445398400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 405454839431283858448386420062420058, 0, 0, 0, 5758010443709145166327844861403225792, 0, 0, 0, 244291442402048155200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2988456197706410400000000000000000, 0, 0, 0, 400560833315592394142881928451629004, 0, 0, 0, 1292775739432819084800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 985481176044048069600000000000000000, 0, 0, 0, 170757957270770661600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 318065342887773495089700018944591328, 0, 0, 0, 4418411628610281487705263541446679744, 0, 0, 0, 192553288299583401600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2243130857004967200000000000000000, 0, 0, 0, 283410010231438387721263833115198816, 0, 0, 0, 984725436860275975200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1250493204666298766400000000000000000, 0, 0, 0, 235895079041969054400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 388128142450196779340660834387926260, 0, 0, 0, 5569595878250632680674445758885765124, 0, 0, 0, 233851898504025216000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2890743301087725600000000000000000, 0, 0, 0, 391519246193473637829796625194649088, 0, 0, 0, 1250474346292493131200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 896507805201396278400000000000000000, 0, 0, 0, 174925618413236409600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 258705326889683103377436370164199728, 0, 0, 0, 4022715767357659056753537405896429216, 0, 0, 0, 155873087338876452000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2042814924773474400000000000000000, 0, 0, 0, 288947424841598386598160755866045530, 0, 0, 0, 897191068111927538400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2334313640263564108800000000000000000, 0, 0, 0, 417940495155808279200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 743324601698603015108661455698515573, 0, 0, 0, 10449852918986087381814549935311917756, 0, 0, 0, 450000603762187838400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5192269377659690400000000000000000, 0, 0, 0, 690366982787152060954732387079498235, 0, 0, 0, 2334352899188300911200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2261437492402947736800000000000000000, 0, 0, 0, 435092921256856852800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 670263004636543618271007670428379200, 0, 0, 0, 10123427156892256865779199823957885120, 0, 0, 0, 405769771738897977600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5032254441212071200000000000000000, 0, 0, 0, 718699641057039858832022762863958100, 0, 0, 0, 2261397046622641034400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (125 * c.1.val + slot c.2) 0 : ℚ) / 2000000000000000000000000000000000000
private def theta (c : Child) : ℚ :=
  ((ReleasedInterior.seed 1 21).region.getD c.1.val 0 : ℚ) / denominator *
    ((ReleasedInterior.splitWeight 1 21 c.1 c.2 + ReleasedInterior.splitWeight 1 21 c.1
      (complement (ReleasedInterior.parent_total 21 c.1) c.2) : ℕ) : ℚ) / denominator / 2
private def bn0 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 136292328434, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25443711652, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25754580006, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 315059887, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 136291700944, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b0 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℚ := (bn0 c z : ℚ) / 1000000000000
private def v0 (z : Fin 3) : ℚ := ((![36249640627023, 36165255517389, 36249640605083] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn1 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 103894977013, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18002265773, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20300052348, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 236483491, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 103815302731, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b1 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℚ := (bn1 c z : ℚ) / 1000000000000
private def v1 (z : Fin 3) : ℚ := ((![36249640627022, 36245583124786, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn2 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131834037942, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24869388082, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24653984480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 304758443, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131832049786, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b2 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℚ := (bn2 c z : ℚ) / 1000000000000
private def v2 (z : Fin 3) : ℚ := ((![36249640598841, 36165255028789, 36249640526949] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn3 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94514903052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18441644088, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16433018935, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 215365057, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94586936477, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b3 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℚ := (bn3 c z : ℚ) / 1000000000000
private def v3 (z : Fin 3) : ℚ := ((![36077370863541, 36245594159752, 36249640526988] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn4 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 246096493664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44061641351, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47441598602, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 547398287, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 246100632561, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b4 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℚ := (bn4 c z : ℚ) / 1000000000000
private def v4 (z : Fin 3) : ℚ := ((![36077383286113, 36249461772018, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn5 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238413479629, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45869946734, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42778535128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 530528611, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238409215607, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b5 (c : ReleasedInterior.Split 21) (z : Fin 3) : ℚ := (bn5 c z : ℚ) / 1000000000000
private def v5 (z : Fin 3) : ℚ := ((![36077370863541, 36249461772077, 36077383159860] : Fin 3 → ℕ) z : ℚ) / 1000000000000

/-- One complete released parent has a certified normalized child table,
valid for every boundary free mode and every interior grade-two mode. -/
theorem solution :
    ∃ q : Cell 4 6 (ReleasedInterior.parent 21) → ℝ,
      (∑ c, q c) = (8415009414174770924846194048644864209 / 250000000000000000000000000000000000 : ℝ) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 21 (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 1 21 (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 1 21).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 1 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 1 21).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 1 21 c.1 c.2 + ReleasedInterior.splitWeight 1 21 c.1
            (complement (ReleasedInterior.parent_total 21 c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  refine ⟨fun c ↦ (q c : ℝ), ?_, ?_, ?_⟩
  · have hs : (∑ c, q c) = (8415009414174770924846194048644864209 / 250000000000000000000000000000000000 : ℚ) := by decide +kernel
    have hsR := congrArg (fun x : ℚ ↦ (x : ℝ)) hs
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hsR
  · rintro ⟨r, c⟩ z hz
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3), (c.val z).val = 0 →
          q ⟨0, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b0 c z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b0 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region0_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn0 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3), (c.val z).val = 0 →
          q ⟨1, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b1 c z := by decide +kernel
      have hqr : (q ⟨1, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b1 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region1_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn1 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3), (c.val z).val = 0 →
          q ⟨2, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b2 c z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b2 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region2_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn2 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3), (c.val z).val = 0 →
          q ⟨3, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b3 c z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b3 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region3_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn3 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3), (c.val z).val = 0 →
          q ⟨4, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b4 c z := by decide +kernel
      have hqr : (q ⟨4, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b4 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region4_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn4 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3), (c.val z).val = 0 →
          q ⟨5, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b5 c z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b5 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region5_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn5 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
  · rintro ⟨r, c⟩ z hz
    dsimp only
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨0, c⟩ ≤ theta ⟨0, c⟩ * v0 z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ (theta ⟨0, c⟩ : ℝ) * (v0 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region0_112_weight_rate_bound c z hz
      simp only [v0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨0, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨1, c⟩ ≤ theta ⟨1, c⟩ * v1 z := by decide +kernel
      have hqr : (q ⟨1, c⟩ : ℝ) ≤ (theta ⟨1, c⟩ : ℝ) * (v1 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region1_112_weight_rate_bound c z hz
      simp only [v1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨1, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨2, c⟩ ≤ theta ⟨2, c⟩ * v2 z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ (theta ⟨2, c⟩ : ℝ) * (v2 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region2_112_weight_rate_bound c z hz
      simp only [v2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨2, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨3, c⟩ ≤ theta ⟨3, c⟩ * v3 z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ (theta ⟨3, c⟩ : ℝ) * (v3 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region3_112_weight_rate_bound c z hz
      simp only [v3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨3, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨4, c⟩ ≤ theta ⟨4, c⟩ * v4 z := by decide +kernel
      have hqr : (q ⟨4, c⟩ : ℝ) ≤ (theta ⟨4, c⟩ : ℝ) * (v4 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region4_112_weight_rate_bound c z hz
      simp only [v4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨4, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 21) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨5, c⟩ ≤ theta ⟨5, c⟩ * v5 z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ (theta ⟨5, c⟩ : ℝ) * (v5 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell21_region5_112_weight_rate_bound c z hz
      simp only [v5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨5, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
