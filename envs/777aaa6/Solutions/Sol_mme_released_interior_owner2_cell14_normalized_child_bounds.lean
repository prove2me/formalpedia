-- Prove2me | solution 1 for mme_released_interior_owner2_cell14_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T15:39:50.593186+00:00
-- url     : https://prove2.me/submissions/35e82785-e0a2-494f-81c0-cd8485dd1673

import Theorems.Thm_mme_released_interior_owner2_cell14_region0_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region2_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region3_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region4_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region5_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region0_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region2_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region3_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region4_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell14_region5_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_zero_region_volume

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

private abbrev Child := Cell 4 6 (ReleasedInterior.parent 14)
private def slot (c : ReleasedInterior.Split 14) : ℕ := 25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val
private def q (c : Child) : ℚ :=
  (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 474230073265266506400000000000000000, 0, 0, 0, 597112078324661150400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22265877717832513708523735215181961, 0, 0, 0, 990986896418418907127047840411887726, 0, 0, 0, 331321546804286822400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 620939509882085102400000000000000000, 0, 0, 0, 781519220343197856000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29156424098957904170462868921055284, 0, 0, 0, 1297035035517340145443876414684409600, 0, 0, 0, 433820323863799401600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3992061172551580497600000000000000000, 0, 0, 0, 5045025898720533204000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186720317641398668653145508333362736, 0, 0, 0, 8333526300562488324247287407055628830, 0, 0, 0, 2794982070128628009600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2316865642003756720800000000000000000, 0, 0, 0, 2942693589168583106400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 108141794722285891378930504077219612, 0, 0, 0, 4860893496683396427053690143402157826, 0, 0, 0, 1621968679653097744800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3548041840001404015200000000000000000, 0, 0, 0, 4499269904077995060000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 166314848450017629886519033028974464, 0, 0, 0, 7432030049334733999070489104958724954, 0, 0, 0, 2484138189239327030400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (125 * c.1.val + slot c.2) 0 : ℚ) / 2000000000000000000000000000000000000
private def theta (c : Child) : ℚ :=
  ((ReleasedInterior.seed 2 14).region.getD c.1.val 0 : ℚ) / denominator *
    ((ReleasedInterior.splitWeight 2 14 c.1 c.2 + ReleasedInterior.splitWeight 2 14 c.1
      (complement (ReleasedInterior.parent_total 14 c.1) c.2) : ℕ) : ℚ) / denominator / 2
private def bn0 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49996005767, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62950918962, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34929783872, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b0 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℚ := (bn0 c z : ℚ) / 1000000000000
private def v0 (z : Fin 3) : ℚ := ((![36077370863541, 36247789431159, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn2 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65462941022, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82392158680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45735782348, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b2 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℚ := (bn2 c z : ℚ) / 1000000000000
private def v2 (z : Fin 3) : ℚ := ((![36077370863541, 36247788450955, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn3 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 420865576978, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 531875049995, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 294662754588, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b3 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℚ := (bn3 c z : ℚ) / 1000000000000
private def v3 (z : Fin 3) : ℚ := ((![36077370863541, 36077370863541, 36249640527686] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn4 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244257027399, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 310235335017, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170997075119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b4 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℚ := (bn4 c z : ℚ) / 1000000000000
private def v4 (z : Fin 3) : ℚ := ((![36077370863541, 36077840402903, 36249640527398] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn5 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 374054557681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 474338378675, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 261891841612, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b5 (c : ReleasedInterior.Split 14) (z : Fin 3) : ℚ := (bn5 c z : ℚ) / 1000000000000
private def v5 (z : Fin 3) : ℚ := ((![36077370863541, 36077370863541, 36249640527542] : Fin 3 → ℕ) z : ℚ) / 1000000000000

/-- One complete released parent has a certified normalized child table,
valid for every boundary free mode and every interior grade-two mode. -/
theorem solution :
    ∃ q : Cell 4 6 (ReleasedInterior.parent 14) → ℝ,
      (∑ c, q c) = (55911060779175072638739972560088602993 / 2000000000000000000000000000000000000 : ℝ) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 2 14 (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 2 14 (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 2 14).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 2 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 2 14).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 2 14 c.1 c.2 + ReleasedInterior.splitWeight 2 14 c.1
            (complement (ReleasedInterior.parent_total 14 c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  refine ⟨fun c ↦ (q c : ℝ), ?_, ?_, ?_⟩
  · have hs : (∑ c, q c) = (55911060779175072638739972560088602993 / 2000000000000000000000000000000000000 : ℚ) := by decide +kernel
    have hsR := congrArg (fun x : ℚ ↦ (x : ℝ)) hs
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hsR
  · rintro ⟨r, c⟩ z hz
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3), (c.val z).val = 0 →
          q ⟨0, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b0 c z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b0 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region0_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn0 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hzero : (ReleasedInterior.seed 2 14).region.getD 1 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 14, q ⟨1, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 2 14 ⟨1, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨1, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 2 14 (z + 1) ⟨1, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 2 14 (z + 1) ⟨1, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3), (c.val z).val = 0 →
          q ⟨2, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b2 c z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b2 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region2_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn2 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3), (c.val z).val = 0 →
          q ⟨3, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b3 c z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b3 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region3_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn3 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3), (c.val z).val = 0 →
          q ⟨4, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b4 c z := by decide +kernel
      have hqr : (q ⟨4, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b4 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region4_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn4 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3), (c.val z).val = 0 →
          q ⟨5, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b5 c z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b5 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region5_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn5 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
  · rintro ⟨r, c⟩ z hz
    dsimp only
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨0, c⟩ ≤ theta ⟨0, c⟩ * v0 z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ (theta ⟨0, c⟩ : ℝ) * (v0 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region0_112_weight_rate_bound c z hz
      simp only [v0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨0, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hqzero : ∀ c : ReleasedInterior.Split 14, q ⟨1, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 14, theta ⟨1, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨1, c⟩ : ℝ) ≤ (theta ⟨1, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨2, c⟩ ≤ theta ⟨2, c⟩ * v2 z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ (theta ⟨2, c⟩ : ℝ) * (v2 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region2_112_weight_rate_bound c z hz
      simp only [v2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨2, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨3, c⟩ ≤ theta ⟨3, c⟩ * v3 z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ (theta ⟨3, c⟩ : ℝ) * (v3 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region3_112_weight_rate_bound c z hz
      simp only [v3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨3, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨4, c⟩ ≤ theta ⟨4, c⟩ * v4 z := by decide +kernel
      have hqr : (q ⟨4, c⟩ : ℝ) ≤ (theta ⟨4, c⟩ : ℝ) * (v4 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region4_112_weight_rate_bound c z hz
      simp only [v4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨4, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 14) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨5, c⟩ ≤ theta ⟨5, c⟩ * v5 z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ (theta ⟨5, c⟩ : ℝ) * (v5 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner2_cell14_region5_112_weight_rate_bound c z hz
      simp only [v5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨5, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
