-- Prove2me | solution 1 for mme_released_recursive_level2_cert7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:40:40.498763+00:00
-- url     : https://prove2.me/submissions/68f9dcb9-9c91-4244-b4a0-752205d9f3c1

import Mathlib
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_floor_cases
import Theorems.Thm_mme_released_recursive_level2_marginals
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace MME.L2Cert

theorem logLo0 : logLo 0 = 693147180559945309417232/10^24 :=
  mme_released_recursive_level2_floor_cases.1.1
theorem logHi0 : logHi 0 = 693147180559945309417233/10^24 :=
  mme_released_recursive_level2_floor_cases.1.2.1
theorem logLo1 : logLo 1 = 1098612288668109691395245/10^24 :=
  mme_released_recursive_level2_floor_cases.1.2.2.1
theorem logHi1 : logHi 1 = 1098612288668109691395246/10^24 :=
  mme_released_recursive_level2_floor_cases.1.2.2.2.1
theorem logLo2 : logLo 2 = 1609437912434100374600759/10^24 :=
  mme_released_recursive_level2_floor_cases.1.2.2.2.2.1
theorem logHi2 : logHi 2 = 1609437912434100374600760/10^24 :=
  mme_released_recursive_level2_floor_cases.1.2.2.2.2.2.1
theorem logLo3 : logLo 3 = 1945910149055313305105352/10^24 :=
  mme_released_recursive_level2_floor_cases.1.2.2.2.2.2.2.1
theorem logHi3 : logHi 3 = 1945910149055313305105353/10^24 :=
  mme_released_recursive_level2_floor_cases.1.2.2.2.2.2.2.2

theorem PG_param0 (i : Fin 3) (r : Fin 1104) (h : parent2 r i = 2) :
    PG i r 0 = ((l2At r).2.2 : ℚ) / (D : ℚ) :=
  (mme_released_recursive_level2_floor_cases.2.2.2 i r h).1
theorem PG_param1 (i : Fin 3) (r : Fin 1104) (h : parent2 r i = 2) :
    PG i r 1 = ((D - 2 * (l2At r).2.2 : ℕ) : ℚ) / (D : ℚ) :=
  (mme_released_recursive_level2_floor_cases.2.2.2 i r h).2.1
theorem PG_param2 (i : Fin 3) (r : Fin 1104) (h : parent2 r i = 2) :
    PG i r 2 = ((l2At r).2.2 : ℚ) / (D : ℚ) :=
  (mme_released_recursive_level2_floor_cases.2.2.2 i r h).2.2

end MME.L2Cert

namespace MME.L2Cert

theorem cert_644 :
    ((certNum ⟨644, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨644, by omega⟩) ⟨644, by omega⟩ (certE ⟨644, by omega⟩) := by
  have hm : certMode (⟨644, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨644, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨644, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨644, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨644, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_645 :
    ((certNum ⟨645, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨645, by omega⟩) ⟨645, by omega⟩ (certE ⟨645, by omega⟩) := by
  have hm : certMode (⟨645, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨645, by omega⟩ : Fin 1104) = 203880739127026868663996146146 := by decide +kernel
  have he : certE (⟨645, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨645, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨645, by omega⟩ : Fin 1104)).2.2 = 21068031670 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_646 :
    ((certNum ⟨646, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨646, by omega⟩) ⟨646, by omega⟩ (certE ⟨646, by omega⟩) := by
  have hm : certMode (⟨646, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨646, by omega⟩ : Fin 1104) = 177418646588741546722456858784 := by decide +kernel
  have he : certE (⟨646, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then -30 else if j.val = 1 then 5 else if j.val = 2 then 7 else 0)) := by decide +kernel
  have hp : parent2 (⟨646, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨646, by omega⟩ : Fin 1104)).2.2 = 17680294539 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_647 :
    ((certNum ⟨647, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨647, by omega⟩) ⟨647, by omega⟩ (certE ⟨647, by omega⟩) := by
  have hm : certMode (⟨647, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨647, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨647, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨647, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨647, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_648 :
    ((certNum ⟨648, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨648, by omega⟩) ⟨648, by omega⟩ (certE ⟨648, by omega⟩) := by
  have hm : certMode (⟨648, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨648, by omega⟩ : Fin 1104) = 39822507454917504633186032430 := by decide +kernel
  have he : certE (⟨648, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -37 else if j.val = 1 then -2 else if j.val = 2 then 4 else 8)) := by decide +kernel
  have hp : parent2 (⟨648, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨648, by omega⟩ : Fin 1104)).2.2 = 2912827939 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_649 :
    ((certNum ⟨649, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨649, by omega⟩) ⟨649, by omega⟩ (certE ⟨649, by omega⟩) := by
  have hm : certMode (⟨649, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨649, by omega⟩ : Fin 1104) = 203782104110073993498776648477 := by decide +kernel
  have he : certE (⟨649, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨649, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨649, by omega⟩ : Fin 1104)).2.2 = 21055111884 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_650 :
    ((certNum ⟨650, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨650, by omega⟩) ⟨650, by omega⟩ (certE ⟨650, by omega⟩) := by
  have hm : certMode (⟨650, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨650, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨650, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨650, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨650, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_651 :
    ((certNum ⟨651, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨651, by omega⟩) ⟨651, by omega⟩ (certE ⟨651, by omega⟩) := by
  have hm : certMode (⟨651, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨651, by omega⟩ : Fin 1104) = 203779125393255189900739900316 := by decide +kernel
  have he : certE (⟨651, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨651, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨651, by omega⟩ : Fin 1104)).2.2 = 21054721757 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_652 :
    ((certNum ⟨652, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨652, by omega⟩) ⟨652, by omega⟩ (certE ⟨652, by omega⟩) := by
  have hm : certMode (⟨652, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨652, by omega⟩ : Fin 1104) = 203946073404663746589595953865 := by decide +kernel
  have he : certE (⟨652, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨652, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨652, by omega⟩ : Fin 1104)).2.2 = 21076590745 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_653 :
    ((certNum ⟨653, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨653, by omega⟩) ⟨653, by omega⟩ (certE ⟨653, by omega⟩) := by
  have hm : certMode (⟨653, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨653, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨653, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨653, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨653, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_654 :
    ((certNum ⟨654, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨654, by omega⟩) ⟨654, by omega⟩ (certE ⟨654, by omega⟩) := by
  have hm : certMode (⟨654, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨654, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨654, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨654, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨654, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_655 :
    ((certNum ⟨655, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨655, by omega⟩) ⟨655, by omega⟩ (certE ⟨655, by omega⟩) := by
  have hm : certMode (⟨655, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨655, by omega⟩ : Fin 1104) = 203778356274441685257769480893 := by decide +kernel
  have he : certE (⟨655, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨655, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨655, by omega⟩ : Fin 1104)).2.2 = 21054621025 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_656 :
    ((certNum ⟨656, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨656, by omega⟩) ⟨656, by omega⟩ (certE ⟨656, by omega⟩) := by
  have hm : certMode (⟨656, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨656, by omega⟩ : Fin 1104) = 203946063627003657180390034801 := by decide +kernel
  have he : certE (⟨656, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨656, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨656, by omega⟩ : Fin 1104)).2.2 = 21076589464 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_657 :
    ((certNum ⟨657, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨657, by omega⟩) ⟨657, by omega⟩ (certE ⟨657, by omega⟩) := by
  have hm : certMode (⟨657, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨657, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨657, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨657, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨657, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_658 :
    ((certNum ⟨658, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨658, by omega⟩) ⟨658, by omega⟩ (certE ⟨658, by omega⟩) := by
  have hm : certMode (⟨658, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨658, by omega⟩ : Fin 1104) = 10613596703228909576988346218 := by decide +kernel
  have he : certE (⟨658, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 5 else if j.val = 1 then -1 else if j.val = 2 then 0 else -5)) := by decide +kernel
  have hp : parent2 (⟨658, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨658, by omega⟩ : Fin 1104)).2.2 = 634647479 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_659 :
    ((certNum ⟨659, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨659, by omega⟩) ⟨659, by omega⟩ (certE ⟨659, by omega⟩) := by
  have hm : certMode (⟨659, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨659, by omega⟩ : Fin 1104) = 202772590931638946040440703002 := by decide +kernel
  have he : certE (⟨659, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨659, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨659, by omega⟩ : Fin 1104)).2.2 = 20923006728 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_660 :
    ((certNum ⟨660, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨660, by omega⟩) ⟨660, by omega⟩ (certE ⟨660, by omega⟩) := by
  have hm : certMode (⟨660, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨660, by omega⟩ : Fin 1104) = 18679854021499205753561068833 := by decide +kernel
  have he : certE (⟨660, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -8 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨660, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨660, by omega⟩ : Fin 1104)).2.2 = 1210545003 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_661 :
    ((certNum ⟨661, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨661, by omega⟩) ⟨661, by omega⟩ (certE ⟨661, by omega⟩) := by
  have hm : certMode (⟨661, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨661, by omega⟩ : Fin 1104) = 202772298482121250208420175108 := by decide +kernel
  have he : certE (⟨661, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨661, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨661, by omega⟩ : Fin 1104)).2.2 = 20922968491 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_662 :
    ((certNum ⟨662, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨662, by omega⟩) ⟨662, by omega⟩ (certE ⟨662, by omega⟩) := by
  have hm : certMode (⟨662, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨662, by omega⟩ : Fin 1104) = 10613968723457510830283306344 := by decide +kernel
  have he : certE (⟨662, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 5 else if j.val = 1 then -1 else if j.val = 2 then 0 else -5)) := by decide +kernel
  have hp : parent2 (⟨662, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨662, by omega⟩ : Fin 1104)).2.2 = 634672748 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_663 :
    ((certNum ⟨663, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨663, by omega⟩) ⟨663, by omega⟩ (certE ⟨663, by omega⟩) := by
  have hm : certMode (⟨663, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨663, by omega⟩ : Fin 1104) = 202772420381375083062259299843 := by decide +kernel
  have he : certE (⟨663, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨663, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨663, by omega⟩ : Fin 1104)).2.2 = 20922984429 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_664 :
    ((certNum ⟨664, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨664, by omega⟩) ⟨664, by omega⟩ (certE ⟨664, by omega⟩) := by
  have hm : certMode (⟨664, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨664, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨664, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨664, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨664, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_665 :
    ((certNum ⟨665, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨665, by omega⟩) ⟨665, by omega⟩ (certE ⟨665, by omega⟩) := by
  have hm : certMode (⟨665, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨665, by omega⟩ : Fin 1104) = 190817137000132479095625096473 := by decide +kernel
  have he : certE (⟨665, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨665, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨665, by omega⟩ : Fin 1104)).2.2 = 19375852279 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_666 :
    ((certNum ⟨666, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨666, by omega⟩) ⟨666, by omega⟩ (certE ⟨666, by omega⟩) := by
  have hm : certMode (⟨666, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨666, by omega⟩ : Fin 1104) = 202772257961201078110172026663 := by decide +kernel
  have he : certE (⟨666, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨666, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨666, by omega⟩ : Fin 1104)).2.2 = 20922963193 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_667 :
    ((certNum ⟨667, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨667, by omega⟩) ⟨667, by omega⟩ (certE ⟨667, by omega⟩) := by
  have hm : certMode (⟨667, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨667, by omega⟩ : Fin 1104) = 90542512733746983295836736558 := by decide +kernel
  have he : certE (⟨667, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then -28 else if j.val = 1 then 2 else if j.val = 2 then -2 else 8)) := by decide +kernel
  have hp : parent2 (⟨667, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨667, by omega⟩ : Fin 1104)).2.2 = 7732695153 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_668 :
    ((certNum ⟨668, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨668, by omega⟩) ⟨668, by omega⟩ (certE ⟨668, by omega⟩) := by
  have hm : certMode (⟨668, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨668, by omega⟩ : Fin 1104) = 181364808101694448751900301008 := by decide +kernel
  have he : certE (⟨668, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then -3 else 6)) := by decide +kernel
  have hp : parent2 (⟨668, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨668, by omega⟩ : Fin 1104)).2.2 = 18175431833 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_669 :
    ((certNum ⟨669, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨669, by omega⟩) ⟨669, by omega⟩ (certE ⟨669, by omega⟩) := by
  have hm : certMode (⟨669, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨669, by omega⟩ : Fin 1104) = 202772250794703288526774687941 := by decide +kernel
  have he : certE (⟨669, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨669, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨669, by omega⟩ : Fin 1104)).2.2 = 20922962256 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_670 :
    ((certNum ⟨670, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨670, by omega⟩) ⟨670, by omega⟩ (certE ⟨670, by omega⟩) := by
  have hm : certMode (⟨670, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨670, by omega⟩ : Fin 1104) = 203304052385664073626789605155 := by decide +kernel
  have he : certE (⟨670, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨670, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨670, by omega⟩ : Fin 1104)).2.2 = 20992525970 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_671 :
    ((certNum ⟨671, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨671, by omega⟩) ⟨671, by omega⟩ (certE ⟨671, by omega⟩) := by
  have hm : certMode (⟨671, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨671, by omega⟩ : Fin 1104) = 181581499479301908388363122480 := by decide +kernel
  have he : certE (⟨671, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 13 else if j.val = 1 then -8 else if j.val = 2 then 1 else -3)) := by decide +kernel
  have hp : parent2 (⟨671, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨671, by omega⟩ : Fin 1104)).2.2 = 18202723635 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_672 :
    ((certNum ⟨672, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨672, by omega⟩) ⟨672, by omega⟩ (certE ⟨672, by omega⟩) := by
  have hm : certMode (⟨672, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨672, by omega⟩ : Fin 1104) = 89362289067539981482215443806 := by decide +kernel
  have he : certE (⟨672, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then -30 else if j.val = 1 then -2 else if j.val = 2 then 4 else 6)) := by decide +kernel
  have hp : parent2 (⟨672, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨672, by omega⟩ : Fin 1104)).2.2 = 7611141317 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_673 :
    ((certNum ⟨673, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨673, by omega⟩) ⟨673, by omega⟩ (certE ⟨673, by omega⟩) := by
  have hm : certMode (⟨673, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨673, by omega⟩ : Fin 1104) = 203304056206387160503904546255 := by decide +kernel
  have he : certE (⟨673, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨673, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨673, by omega⟩ : Fin 1104)).2.2 = 20992526470 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_674 :
    ((certNum ⟨674, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨674, by omega⟩) ⟨674, by omega⟩ (certE ⟨674, by omega⟩) := by
  have hm : certMode (⟨674, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨674, by omega⟩ : Fin 1104) = 190863884569009676981695331580 := by decide +kernel
  have he : certE (⟨674, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hp : parent2 (⟨674, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨674, by omega⟩ : Fin 1104)).2.2 = 19381839419 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_675 :
    ((certNum ⟨675, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨675, by omega⟩) ⟨675, by omega⟩ (certE ⟨675, by omega⟩) := by
  have hm : certMode (⟨675, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨675, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨675, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨675, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨675, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_676 :
    ((certNum ⟨676, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨676, by omega⟩) ⟨676, by omega⟩ (certE ⟨676, by omega⟩) := by
  have hm : certMode (⟨676, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨676, by omega⟩ : Fin 1104) = 180941496031854021432678808333 := by decide +kernel
  have he : certE (⟨676, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 14 else if j.val = 1 then -4 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨676, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨676, by omega⟩ : Fin 1104)).2.2 = 18122147247 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_677 :
    ((certNum ⟨677, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨677, by omega⟩) ⟨677, by omega⟩ (certE ⟨677, by omega⟩) := by
  have hm : certMode (⟨677, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨677, by omega⟩ : Fin 1104) = 91628268872918038327117751645 := by decide +kernel
  have he : certE (⟨677, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -7 else if j.val = 1 then -8 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hp : parent2 (⟨677, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨677, by omega⟩ : Fin 1104)).2.2 = 7844874596 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_678 :
    ((certNum ⟨678, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨678, by omega⟩) ⟨678, by omega⟩ (certE ⟨678, by omega⟩) := by
  have hm : certMode (⟨678, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨678, by omega⟩ : Fin 1104) = 202772255368412677130299742180 := by decide +kernel
  have he : certE (⟨678, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨678, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨678, by omega⟩ : Fin 1104)).2.2 = 20922962854 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_679 :
    ((certNum ⟨679, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨679, by omega⟩) ⟨679, by omega⟩ (certE ⟨679, by omega⟩) := by
  have hm : certMode (⟨679, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨679, by omega⟩ : Fin 1104) = 190641642778438559385203849327 := by decide +kernel
  have he : certE (⟨679, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨679, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨679, by omega⟩ : Fin 1104)).2.2 = 19353380698 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_680 :
    ((certNum ⟨680, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨680, by omega⟩) ⟨680, by omega⟩ (certE ⟨680, by omega⟩) := by
  have hm : certMode (⟨680, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨680, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨680, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨680, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨680, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_681 :
    ((certNum ⟨681, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨681, by omega⟩) ⟨681, by omega⟩ (certE ⟨681, by omega⟩) := by
  have hm : certMode (⟨681, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨681, by omega⟩ : Fin 1104) = 202772263842777041344702105115 := by decide +kernel
  have he : certE (⟨681, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨681, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨681, by omega⟩ : Fin 1104)).2.2 = 20922963962 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_682 :
    ((certNum ⟨682, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨682, by omega⟩) ⟨682, by omega⟩ (certE ⟨682, by omega⟩) := by
  have hm : certMode (⟨682, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨682, by omega⟩ : Fin 1104) = 181450144077379783706263313067 := by decide +kernel
  have he : certE (⟨682, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hp : parent2 (⟨682, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨682, by omega⟩ : Fin 1104)).2.2 = 18186178378 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_683 :
    ((certNum ⟨683, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨683, by omega⟩) ⟨683, by omega⟩ (certE ⟨683, by omega⟩) := by
  have hm : certMode (⟨683, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨683, by omega⟩ : Fin 1104) = 203946155762927474497210098537 := by decide +kernel
  have he : certE (⟨683, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨683, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨683, by omega⟩ : Fin 1104)).2.2 = 21076601535 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_684 :
    ((certNum ⟨684, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨684, by omega⟩) ⟨684, by omega⟩ (certE ⟨684, by omega⟩) := by
  have hm : certMode (⟨684, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨684, by omega⟩ : Fin 1104) = 89065796137456201785484480609 := by decide +kernel
  have he : certE (⟨684, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 16 else if j.val = 1 then -8 else if j.val = 2 then 4 else -7)) := by decide +kernel
  have hp : parent2 (⟨684, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨684, by omega⟩ : Fin 1104)).2.2 = 7580668349 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_685 :
    ((certNum ⟨685, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨685, by omega⟩) ⟨685, by omega⟩ (certE ⟨685, by omega⟩) := by
  have hm : certMode (⟨685, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨685, by omega⟩ : Fin 1104) = 190770118070759087263775861323 := by decide +kernel
  have he : certE (⟨685, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨685, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨685, by omega⟩ : Fin 1104)).2.2 = 19369830943 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_686 :
    ((certNum ⟨686, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨686, by omega⟩) ⟨686, by omega⟩ (certE ⟨686, by omega⟩) := by
  have hm : certMode (⟨686, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨686, by omega⟩ : Fin 1104) = 203946151610667093608703012062 := by decide +kernel
  have he : certE (⟨686, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨686, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨686, by omega⟩ : Fin 1104)).2.2 = 21076600991 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_687 :
    ((certNum ⟨687, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨687, by omega⟩) ⟨687, by omega⟩ (certE ⟨687, by omega⟩) := by
  have hm : certMode (⟨687, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨687, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨687, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨687, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨687, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_688 :
    ((certNum ⟨688, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨688, by omega⟩) ⟨688, by omega⟩ (certE ⟨688, by omega⟩) := by
  have hm : certMode (⟨688, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨688, by omega⟩ : Fin 1104) = 25550702631934738536021829238 := by decide +kernel
  have he : certE (⟨688, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -16 else if j.val = 1 then 7 else if j.val = 2 then 3 else -4)) := by decide +kernel
  have hp : parent2 (⟨688, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨688, by omega⟩ : Fin 1104)).2.2 = 1737268004 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_689 :
    ((certNum ⟨689, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨689, by omega⟩) ⟨689, by omega⟩ (certE ⟨689, by omega⟩) := by
  have hm : certMode (⟨689, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨689, by omega⟩ : Fin 1104) = 202772300661898790417070168182 := by decide +kernel
  have he : certE (⟨689, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨689, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨689, by omega⟩ : Fin 1104)).2.2 = 20922968776 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_690 :
    ((certNum ⟨690, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨690, by omega⟩) ⟨690, by omega⟩ (certE ⟨690, by omega⟩) := by
  have hm : certMode (⟨690, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨690, by omega⟩ : Fin 1104) = 15883388194577647202350528588 := by decide +kernel
  have he : certE (⟨690, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -14 else if j.val = 1 then -6 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨690, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨690, by omega⟩ : Fin 1104)).2.2 = 1005061334 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_691 :
    ((certNum ⟨691, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨691, by omega⟩) ⟨691, by omega⟩ (certE ⟨691, by omega⟩) := by
  have hm : certMode (⟨691, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨691, by omega⟩ : Fin 1104) = 202772498914510388234116215751 := by decide +kernel
  have he : certE (⟨691, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨691, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨691, by omega⟩ : Fin 1104)).2.2 = 20922994697 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_692 :
    ((certNum ⟨692, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨692, by omega⟩) ⟨692, by omega⟩ (certE ⟨692, by omega⟩) := by
  have hm : certMode (⟨692, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨692, by omega⟩ : Fin 1104) = 15884486613448297229882400313 := by decide +kernel
  have he : certE (⟨692, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -14 else if j.val = 1 then -6 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨692, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨692, by omega⟩ : Fin 1104)).2.2 = 1005140922 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_693 :
    ((certNum ⟨693, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨693, by omega⟩) ⟨693, by omega⟩ (certE ⟨693, by omega⟩) := by
  have hm : certMode (⟨693, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨693, by omega⟩ : Fin 1104) = 202772394644712899945256994078 := by decide +kernel
  have he : certE (⟨693, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨693, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨693, by omega⟩ : Fin 1104)).2.2 = 20922981064 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_694 :
    ((certNum ⟨694, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨694, by omega⟩) ⟨694, by omega⟩ (certE ⟨694, by omega⟩) := by
  have hm : certMode (⟨694, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨694, by omega⟩ : Fin 1104) = 203304034191380051701081645007 := by decide +kernel
  have he : certE (⟨694, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨694, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨694, by omega⟩ : Fin 1104)).2.2 = 20992523589 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_695 :
    ((certNum ⟨695, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨695, by omega⟩) ⟨695, by omega⟩ (certE ⟨695, by omega⟩) := by
  have hm : certMode (⟨695, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨695, by omega⟩ : Fin 1104) = 5078602932745172156000536600 := by decide +kernel
  have he : certE (⟨695, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -31 else if j.val = 1 then -5 else if j.val = 2 then 2 else 8)) := by decide +kernel
  have hp : parent2 (⟨695, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨695, by omega⟩ : Fin 1104)).2.2 = 276186480 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_696 :
    ((certNum ⟨696, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨696, by omega⟩) ⟨696, by omega⟩ (certE ⟨696, by omega⟩) := by
  have hm : certMode (⟨696, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨696, by omega⟩ : Fin 1104) = 203304079680908714955997509522 := by decide +kernel
  have he : certE (⟨696, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨696, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨696, by omega⟩ : Fin 1104)).2.2 = 20992529542 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_697 :
    ((certNum ⟨697, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨697, by omega⟩) ⟨697, by omega⟩ (certE ⟨697, by omega⟩) := by
  have hm : certMode (⟨697, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨697, by omega⟩ : Fin 1104) = 10597175025457635758960344370 := by decide +kernel
  have he : certE (⟨697, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -22 else if j.val = 1 then -1 else if j.val = 2 then 8 else -2)) := by decide +kernel
  have hp : parent2 (⟨697, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨697, by omega⟩ : Fin 1104)).2.2 = 633532195 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_698 :
    ((certNum ⟨698, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨698, by omega⟩) ⟨698, by omega⟩ (certE ⟨698, by omega⟩) := by
  have hm : certMode (⟨698, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨698, by omega⟩ : Fin 1104) = 203303722397264892295754782308 := by decide +kernel
  have he : certE (⟨698, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨698, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨698, by omega⟩ : Fin 1104)).2.2 = 20992482786 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_699 :
    ((certNum ⟨699, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨699, by omega⟩) ⟨699, by omega⟩ (certE ⟨699, by omega⟩) := by
  have hm : certMode (⟨699, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨699, by omega⟩ : Fin 1104) = 5078279844411449645554138606 := by decide +kernel
  have he : certE (⟨699, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -31 else if j.val = 1 then -5 else if j.val = 2 then 2 else 8)) := by decide +kernel
  have hp : parent2 (⟨699, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨699, by omega⟩ : Fin 1104)).2.2 = 276166765 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_700 :
    ((certNum ⟨700, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨700, by omega⟩) ⟨700, by omega⟩ (certE ⟨700, by omega⟩) := by
  have hm : certMode (⟨700, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨700, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨700, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨700, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨700, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_701 :
    ((certNum ⟨701, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨701, by omega⟩) ⟨701, by omega⟩ (certE ⟨701, by omega⟩) := by
  have hm : certMode (⟨701, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨701, by omega⟩ : Fin 1104) = 203946200102042481212328891281 := by decide +kernel
  have he : certE (⟨701, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨701, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨701, by omega⟩ : Fin 1104)).2.2 = 21076607344 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_702 :
    ((certNum ⟨702, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨702, by omega⟩) ⟨702, by omega⟩ (certE ⟨702, by omega⟩) := by
  have hm : certMode (⟨702, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨702, by omega⟩ : Fin 1104) = 154705760069551076099817944285 := by decide +kernel
  have he : certE (⟨702, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then 28 else if j.val = 1 then 0 else if j.val = 2 then -5 else -8)) := by decide +kernel
  have hp : parent2 (⟨702, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨702, by omega⟩ : Fin 1104)).2.2 = 14900445100 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_703 :
    ((certNum ⟨703, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨703, by omega⟩) ⟨703, by omega⟩ (certE ⟨703, by omega⟩) := by
  have hm : certMode (⟨703, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨703, by omega⟩ : Fin 1104) = 203973623310552374199220172523 := by decide +kernel
  have he : certE (⟨703, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 1 else if j.val = 1 then -2 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hp : parent2 (⟨703, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨703, by omega⟩ : Fin 1104)).2.2 = 21080200212 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_704 :
    ((certNum ⟨704, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨704, by omega⟩) ⟨704, by omega⟩ (certE ⟨704, by omega⟩) := by
  have hm : certMode (⟨704, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨704, by omega⟩ : Fin 1104) = 203946054727119171352598774310 := by decide +kernel
  have he : certE (⟨704, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨704, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨704, by omega⟩ : Fin 1104)).2.2 = 21076588298 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_705 :
    ((certNum ⟨705, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨705, by omega⟩) ⟨705, by omega⟩ (certE ⟨705, by omega⟩) := by
  have hm : certMode (⟨705, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨705, by omega⟩ : Fin 1104) = 23193263547898499221619528388 := by decide +kernel
  have he : certE (⟨705, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then 14 else if j.val = 1 then -3 else if j.val = 2 then -8 else 0)) := by decide +kernel
  have hp : parent2 (⟨705, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨705, by omega⟩ : Fin 1104)).2.2 = 1553296240 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_706 :
    ((certNum ⟨706, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨706, by omega⟩) ⟨706, by omega⟩ (certE ⟨706, by omega⟩) := by
  have hm : certMode (⟨706, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨706, by omega⟩ : Fin 1104) = 203879797799754048961502421224 := by decide +kernel
  have he : certE (⟨706, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨706, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨706, by omega⟩ : Fin 1104)).2.2 = 21067908362 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_707 :
    ((certNum ⟨707, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨707, by omega⟩) ⟨707, by omega⟩ (certE ⟨707, by omega⟩) := by
  have hm : certMode (⟨707, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨707, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨707, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨707, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨707, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_708 :
    ((certNum ⟨708, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨708, by omega⟩) ⟨708, by omega⟩ (certE ⟨708, by omega⟩) := by
  have hm : certMode (⟨708, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨708, by omega⟩ : Fin 1104) = 154727372878743026822420125217 := by decide +kernel
  have he : certE (⟨708, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -24 else if j.val = 1 then 6 else if j.val = 2 then 0 else 3)) := by decide +kernel
  have hp : parent2 (⟨708, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨708, by omega⟩ : Fin 1104)).2.2 = 14903032886 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_709 :
    ((certNum ⟨709, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨709, by omega⟩) ⟨709, by omega⟩ (certE ⟨709, by omega⟩) := by
  have hm : certMode (⟨709, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨709, by omega⟩ : Fin 1104) = 203880908348506835651050701931 := by decide +kernel
  have he : certE (⟨709, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨709, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨709, by omega⟩ : Fin 1104)).2.2 = 21068053837 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_710 :
    ((certNum ⟨710, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨710, by omega⟩) ⟨710, by omega⟩ (certE ⟨710, by omega⟩) := by
  have hm : certMode (⟨710, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨710, by omega⟩ : Fin 1104) = 204038636052622511897022746472 := by decide +kernel
  have he : certE (⟨710, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨710, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨710, by omega⟩ : Fin 1104)).2.2 = 21088718589 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_711 :
    ((certNum ⟨711, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨711, by omega⟩) ⟨711, by omega⟩ (certE ⟨711, by omega⟩) := by
  have hm : certMode (⟨711, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨711, by omega⟩ : Fin 1104) = 23191703314873493439571568688 := by decide +kernel
  have he : certE (⟨711, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then -33 else if j.val = 1 then 4 else if j.val = 2 then -1 else 7)) := by decide +kernel
  have hp : parent2 (⟨711, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨711, by omega⟩ : Fin 1104)).2.2 = 1553175558 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_712 :
    ((certNum ⟨712, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨712, by omega⟩) ⟨712, by omega⟩ (certE ⟨712, by omega⟩) := by
  have hm : certMode (⟨712, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨712, by omega⟩ : Fin 1104) = 203946067382357922015289789480 := by decide +kernel
  have he : certE (⟨712, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨712, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨712, by omega⟩ : Fin 1104)).2.2 = 21076589956 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_713 :
    ((certNum ⟨713, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨713, by omega⟩) ⟨713, by omega⟩ (certE ⟨713, by omega⟩) := by
  have hm : certMode (⟨713, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨713, by omega⟩ : Fin 1104) = 10492200285473387345671037585 := by decide +kernel
  have he : certE (⟨713, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 15 else if j.val = 1 then -8 else if j.val = 2 then -8 else 2)) := by decide +kernel
  have hp : parent2 (⟨713, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨713, by omega⟩ : Fin 1104)).2.2 = 626409126 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_714 :
    ((certNum ⟨714, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨714, by omega⟩) ⟨714, by omega⟩ (certE ⟨714, by omega⟩) := by
  have hm : certMode (⟨714, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨714, by omega⟩ : Fin 1104) = 203946188599366877128745475230 := by decide +kernel
  have he : certE (⟨714, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨714, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨714, by omega⟩ : Fin 1104)).2.2 = 21076605837 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_715 :
    ((certNum ⟨715, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨715, by omega⟩) ⟨715, by omega⟩ (certE ⟨715, by omega⟩) := by
  have hm : certMode (⟨715, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨715, by omega⟩ : Fin 1104) = 5020415694123017038817252938 := by decide +kernel
  have he : certE (⟨715, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -25 else if j.val = 1 then 5 else if j.val = 2 then -5 else 6)) := by decide +kernel
  have hp : parent2 (⟨715, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨715, by omega⟩ : Fin 1104)).2.2 = 272638647 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_716 :
    ((certNum ⟨716, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨716, by omega⟩) ⟨716, by omega⟩ (certE ⟨716, by omega⟩) := by
  have hm : certMode (⟨716, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨716, by omega⟩ : Fin 1104) = 203946048384233923135686958580 := by decide +kernel
  have he : certE (⟨716, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨716, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨716, by omega⟩ : Fin 1104)).2.2 = 21076587467 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_717 :
    ((certNum ⟨717, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨717, by omega⟩) ⟨717, by omega⟩ (certE ⟨717, by omega⟩) := by
  have hm : certMode (⟨717, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨717, by omega⟩ : Fin 1104) = 5021372242213236634331623827 := by decide +kernel
  have he : certE (⟨717, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -26 else if j.val = 1 then -2 else if j.val = 2 then -1 else 7)) := by decide +kernel
  have hp : parent2 (⟨717, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨717, by omega⟩ : Fin 1104)).2.2 = 272696925 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_718 :
    ((certNum ⟨718, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨718, by omega⟩) ⟨718, by omega⟩ (certE ⟨718, by omega⟩) := by
  have hm : certMode (⟨718, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨718, by omega⟩ : Fin 1104) = 203878443156332454698103793889 := by decide +kernel
  have he : certE (⟨718, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨718, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨718, by omega⟩ : Fin 1104)).2.2 = 21067730904 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_719 :
    ((certNum ⟨719, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨719, by omega⟩) ⟨719, by omega⟩ (certE ⟨719, by omega⟩) := by
  have hm : certMode (⟨719, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨719, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨719, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨719, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨719, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_720 :
    ((certNum ⟨720, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨720, by omega⟩) ⟨720, by omega⟩ (certE ⟨720, by omega⟩) := by
  have hm : certMode (⟨720, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨720, by omega⟩ : Fin 1104) = 203876399380276387133734280107 := by decide +kernel
  have he : certE (⟨720, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨720, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨720, by omega⟩ : Fin 1104)).2.2 = 21067463171 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_721 :
    ((certNum ⟨721, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨721, by omega⟩) ⟨721, by omega⟩ (certE ⟨721, by omega⟩) := by
  have hm : certMode (⟨721, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨721, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨721, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨721, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨721, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_722 :
    ((certNum ⟨722, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨722, by omega⟩) ⟨722, by omega⟩ (certE ⟨722, by omega⟩) := by
  have hm : certMode (⟨722, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨722, by omega⟩ : Fin 1104) = 203878047506128578816990528967 := by decide +kernel
  have he : certE (⟨722, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨722, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨722, by omega⟩ : Fin 1104)).2.2 = 21067679074 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_723 :
    ((certNum ⟨723, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨723, by omega⟩) ⟨723, by omega⟩ (certE ⟨723, by omega⟩) := by
  have hm : certMode (⟨723, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨723, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨723, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨723, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨723, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_724 :
    ((certNum ⟨724, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨724, by omega⟩) ⟨724, by omega⟩ (certE ⟨724, by omega⟩) := by
  have hm : certMode (⟨724, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨724, by omega⟩ : Fin 1104) = 203942476577721768200678786836 := by decide +kernel
  have he : certE (⟨724, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨724, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨724, by omega⟩ : Fin 1104)).2.2 = 21076119517 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_725 :
    ((certNum ⟨725, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨725, by omega⟩) ⟨725, by omega⟩ (certE ⟨725, by omega⟩) := by
  have hm : certMode (⟨725, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨725, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨725, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨725, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨725, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_726 :
    ((certNum ⟨726, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨726, by omega⟩) ⟨726, by omega⟩ (certE ⟨726, by omega⟩) := by
  have hm : certMode (⟨726, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨726, by omega⟩ : Fin 1104) = 203944191615095722495669627050 := by decide +kernel
  have he : certE (⟨726, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨726, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨726, by omega⟩ : Fin 1104)).2.2 = 21076344207 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_727 :
    ((certNum ⟨727, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨727, by omega⟩) ⟨727, by omega⟩ (certE ⟨727, by omega⟩) := by
  have hm : certMode (⟨727, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨727, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨727, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨727, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨727, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_728 :
    ((certNum ⟨728, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨728, by omega⟩) ⟨728, by omega⟩ (certE ⟨728, by omega⟩) := by
  have hm : certMode (⟨728, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨728, by omega⟩ : Fin 1104) = 203944620101909282051480473239 := by decide +kernel
  have he : certE (⟨728, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨728, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨728, by omega⟩ : Fin 1104)).2.2 = 21076400344 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_729 :
    ((certNum ⟨729, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨729, by omega⟩) ⟨729, by omega⟩ (certE ⟨729, by omega⟩) := by
  have hm : certMode (⟨729, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨729, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨729, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨729, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨729, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_730 :
    ((certNum ⟨730, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨730, by omega⟩) ⟨730, by omega⟩ (certE ⟨730, by omega⟩) := by
  have hm : certMode (⟨730, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨730, by omega⟩ : Fin 1104) = 54107472743227748223696790 := by decide +kernel
  have he : certE (⟨730, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -34 else if j.val = 1 then 8 else if j.val = 2 then 1 else 0)) := by decide +kernel
  have hp : parent2 (⟨730, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨730, by omega⟩ : Fin 1104)).2.2 = 1909399 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_731 :
    ((certNum ⟨731, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨731, by omega⟩) ⟨731, by omega⟩ (certE ⟨731, by omega⟩) := by
  have hm : certMode (⟨731, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨731, by omega⟩ : Fin 1104) = 54107472743227748223696790 := by decide +kernel
  have he : certE (⟨731, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -34 else if j.val = 1 then 8 else if j.val = 2 then 1 else 0)) := by decide +kernel
  have hp : parent2 (⟨731, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨731, by omega⟩ : Fin 1104)).2.2 = 1909399 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_732 :
    ((certNum ⟨732, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨732, by omega⟩) ⟨732, by omega⟩ (certE ⟨732, by omega⟩) := by
  have hm : certMode (⟨732, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨732, by omega⟩ : Fin 1104) = 78112906669399665802115142 := by decide +kernel
  have he : certE (⟨732, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -10 else if j.val = 1 then -3 else if j.val = 2 then -4 else 2)) := by decide +kernel
  have hp : parent2 (⟨732, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨732, by omega⟩ : Fin 1104)).2.2 = 2835680 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_733 :
    ((certNum ⟨733, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨733, by omega⟩) ⟨733, by omega⟩ (certE ⟨733, by omega⟩) := by
  have hm : certMode (⟨733, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨733, by omega⟩ : Fin 1104) = 78002283987916452639520144 := by decide +kernel
  have he : certE (⟨733, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -41 else if j.val = 1 then 3 else if j.val = 2 then -2 else 8)) := by decide +kernel
  have hp : parent2 (⟨733, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨733, by omega⟩ : Fin 1104)).2.2 = 2831350 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_734 :
    ((certNum ⟨734, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨734, by omega⟩) ⟨734, by omega⟩ (certE ⟨734, by omega⟩) := by
  have hm : certMode (⟨734, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨734, by omega⟩ : Fin 1104) = 78112753390899692196491688 := by decide +kernel
  have he : certE (⟨734, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -10 else if j.val = 1 then -3 else if j.val = 2 then -4 else 2)) := by decide +kernel
  have hp : parent2 (⟨734, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨734, by omega⟩ : Fin 1104)).2.2 = 2835674 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_735 :
    ((certNum ⟨735, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨735, by omega⟩) ⟨735, by omega⟩ (certE ⟨735, by omega⟩) := by
  have hm : certMode (⟨735, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨735, by omega⟩ : Fin 1104) = 78002181790222266308644039 := by decide +kernel
  have he : certE (⟨735, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -41 else if j.val = 1 then 3 else if j.val = 2 then -2 else 8)) := by decide +kernel
  have hp : parent2 (⟨735, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨735, by omega⟩ : Fin 1104)).2.2 = 2831346 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨644 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨644 + j.val, by omega⟩) ⟨644 + j.val, by omega⟩
        (certE ⟨644 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_644
  | ⟨1, _⟩ => exact MME.L2Cert.cert_645
  | ⟨2, _⟩ => exact MME.L2Cert.cert_646
  | ⟨3, _⟩ => exact MME.L2Cert.cert_647
  | ⟨4, _⟩ => exact MME.L2Cert.cert_648
  | ⟨5, _⟩ => exact MME.L2Cert.cert_649
  | ⟨6, _⟩ => exact MME.L2Cert.cert_650
  | ⟨7, _⟩ => exact MME.L2Cert.cert_651
  | ⟨8, _⟩ => exact MME.L2Cert.cert_652
  | ⟨9, _⟩ => exact MME.L2Cert.cert_653
  | ⟨10, _⟩ => exact MME.L2Cert.cert_654
  | ⟨11, _⟩ => exact MME.L2Cert.cert_655
  | ⟨12, _⟩ => exact MME.L2Cert.cert_656
  | ⟨13, _⟩ => exact MME.L2Cert.cert_657
  | ⟨14, _⟩ => exact MME.L2Cert.cert_658
  | ⟨15, _⟩ => exact MME.L2Cert.cert_659
  | ⟨16, _⟩ => exact MME.L2Cert.cert_660
  | ⟨17, _⟩ => exact MME.L2Cert.cert_661
  | ⟨18, _⟩ => exact MME.L2Cert.cert_662
  | ⟨19, _⟩ => exact MME.L2Cert.cert_663
  | ⟨20, _⟩ => exact MME.L2Cert.cert_664
  | ⟨21, _⟩ => exact MME.L2Cert.cert_665
  | ⟨22, _⟩ => exact MME.L2Cert.cert_666
  | ⟨23, _⟩ => exact MME.L2Cert.cert_667
  | ⟨24, _⟩ => exact MME.L2Cert.cert_668
  | ⟨25, _⟩ => exact MME.L2Cert.cert_669
  | ⟨26, _⟩ => exact MME.L2Cert.cert_670
  | ⟨27, _⟩ => exact MME.L2Cert.cert_671
  | ⟨28, _⟩ => exact MME.L2Cert.cert_672
  | ⟨29, _⟩ => exact MME.L2Cert.cert_673
  | ⟨30, _⟩ => exact MME.L2Cert.cert_674
  | ⟨31, _⟩ => exact MME.L2Cert.cert_675
  | ⟨32, _⟩ => exact MME.L2Cert.cert_676
  | ⟨33, _⟩ => exact MME.L2Cert.cert_677
  | ⟨34, _⟩ => exact MME.L2Cert.cert_678
  | ⟨35, _⟩ => exact MME.L2Cert.cert_679
  | ⟨36, _⟩ => exact MME.L2Cert.cert_680
  | ⟨37, _⟩ => exact MME.L2Cert.cert_681
  | ⟨38, _⟩ => exact MME.L2Cert.cert_682
  | ⟨39, _⟩ => exact MME.L2Cert.cert_683
  | ⟨40, _⟩ => exact MME.L2Cert.cert_684
  | ⟨41, _⟩ => exact MME.L2Cert.cert_685
  | ⟨42, _⟩ => exact MME.L2Cert.cert_686
  | ⟨43, _⟩ => exact MME.L2Cert.cert_687
  | ⟨44, _⟩ => exact MME.L2Cert.cert_688
  | ⟨45, _⟩ => exact MME.L2Cert.cert_689
  | ⟨46, _⟩ => exact MME.L2Cert.cert_690
  | ⟨47, _⟩ => exact MME.L2Cert.cert_691
  | ⟨48, _⟩ => exact MME.L2Cert.cert_692
  | ⟨49, _⟩ => exact MME.L2Cert.cert_693
  | ⟨50, _⟩ => exact MME.L2Cert.cert_694
  | ⟨51, _⟩ => exact MME.L2Cert.cert_695
  | ⟨52, _⟩ => exact MME.L2Cert.cert_696
  | ⟨53, _⟩ => exact MME.L2Cert.cert_697
  | ⟨54, _⟩ => exact MME.L2Cert.cert_698
  | ⟨55, _⟩ => exact MME.L2Cert.cert_699
  | ⟨56, _⟩ => exact MME.L2Cert.cert_700
  | ⟨57, _⟩ => exact MME.L2Cert.cert_701
  | ⟨58, _⟩ => exact MME.L2Cert.cert_702
  | ⟨59, _⟩ => exact MME.L2Cert.cert_703
  | ⟨60, _⟩ => exact MME.L2Cert.cert_704
  | ⟨61, _⟩ => exact MME.L2Cert.cert_705
  | ⟨62, _⟩ => exact MME.L2Cert.cert_706
  | ⟨63, _⟩ => exact MME.L2Cert.cert_707
  | ⟨64, _⟩ => exact MME.L2Cert.cert_708
  | ⟨65, _⟩ => exact MME.L2Cert.cert_709
  | ⟨66, _⟩ => exact MME.L2Cert.cert_710
  | ⟨67, _⟩ => exact MME.L2Cert.cert_711
  | ⟨68, _⟩ => exact MME.L2Cert.cert_712
  | ⟨69, _⟩ => exact MME.L2Cert.cert_713
  | ⟨70, _⟩ => exact MME.L2Cert.cert_714
  | ⟨71, _⟩ => exact MME.L2Cert.cert_715
  | ⟨72, _⟩ => exact MME.L2Cert.cert_716
  | ⟨73, _⟩ => exact MME.L2Cert.cert_717
  | ⟨74, _⟩ => exact MME.L2Cert.cert_718
  | ⟨75, _⟩ => exact MME.L2Cert.cert_719
  | ⟨76, _⟩ => exact MME.L2Cert.cert_720
  | ⟨77, _⟩ => exact MME.L2Cert.cert_721
  | ⟨78, _⟩ => exact MME.L2Cert.cert_722
  | ⟨79, _⟩ => exact MME.L2Cert.cert_723
  | ⟨80, _⟩ => exact MME.L2Cert.cert_724
  | ⟨81, _⟩ => exact MME.L2Cert.cert_725
  | ⟨82, _⟩ => exact MME.L2Cert.cert_726
  | ⟨83, _⟩ => exact MME.L2Cert.cert_727
  | ⟨84, _⟩ => exact MME.L2Cert.cert_728
  | ⟨85, _⟩ => exact MME.L2Cert.cert_729
  | ⟨86, _⟩ => exact MME.L2Cert.cert_730
  | ⟨87, _⟩ => exact MME.L2Cert.cert_731
  | ⟨88, _⟩ => exact MME.L2Cert.cert_732
  | ⟨89, _⟩ => exact MME.L2Cert.cert_733
  | ⟨90, _⟩ => exact MME.L2Cert.cert_734
  | ⟨91, _⟩ => exact MME.L2Cert.cert_735
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
