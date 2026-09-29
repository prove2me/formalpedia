-- Prove2me | solution 1 for mme_released_recursive_level2_cert8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:47:31.322627+00:00
-- url     : https://prove2.me/submissions/efd7975e-8f6a-4fcf-8fed-b4101eae2e8f

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

theorem cert_736 :
    ((certNum ⟨736, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨736, by omega⟩) ⟨736, by omega⟩ (certE ⟨736, by omega⟩) := by
  have hm : certMode (⟨736, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨736, by omega⟩ : Fin 1104) = 203944564221652508400864916491 := by decide +kernel
  have he : certE (⟨736, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨736, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨736, by omega⟩ : Fin 1104)).2.2 = 21076393023 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_737 :
    ((certNum ⟨737, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨737, by omega⟩) ⟨737, by omega⟩ (certE ⟨737, by omega⟩) := by
  have hm : certMode (⟨737, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨737, by omega⟩ : Fin 1104) = 203944553192151043429943393388 := by decide +kernel
  have he : certE (⟨737, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨737, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨737, by omega⟩ : Fin 1104)).2.2 = 21076391578 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_738 :
    ((certNum ⟨738, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨738, by omega⟩) ⟨738, by omega⟩ (certE ⟨738, by omega⟩) := by
  have hm : certMode (⟨738, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨738, by omega⟩ : Fin 1104) = 203944564229285381243749456461 := by decide +kernel
  have he : certE (⟨738, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨738, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨738, by omega⟩ : Fin 1104)).2.2 = 21076393024 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_739 :
    ((certNum ⟨739, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨739, by omega⟩) ⟨739, by omega⟩ (certE ⟨739, by omega⟩) := by
  have hm : certMode (⟨739, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨739, by omega⟩ : Fin 1104) = 203944553184518170300549841285 := by decide +kernel
  have he : certE (⟨739, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨739, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨739, by omega⟩ : Fin 1104)).2.2 = 21076391577 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_740 :
    ((certNum ⟨740, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨740, by omega⟩) ⟨740, by omega⟩ (certE ⟨740, by omega⟩) := by
  have hm : certMode (⟨740, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨740, by omega⟩ : Fin 1104) = 203944551253401262197576547136 := by decide +kernel
  have he : certE (⟨740, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨740, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨740, by omega⟩ : Fin 1104)).2.2 = 21076391324 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_741 :
    ((certNum ⟨741, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨741, by omega⟩) ⟨741, by omega⟩ (certE ⟨741, by omega⟩) := by
  have hm : certMode (⟨741, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨741, by omega⟩ : Fin 1104) = 203944551253401262197576547136 := by decide +kernel
  have he : certE (⟨741, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨741, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨741, by omega⟩ : Fin 1104)).2.2 = 21076391324 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_742 :
    ((certNum ⟨742, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨742, by omega⟩) ⟨742, by omega⟩ (certE ⟨742, by omega⟩) := by
  have hm : certMode (⟨742, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨742, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨742, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨742, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨742, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_743 :
    ((certNum ⟨743, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨743, by omega⟩) ⟨743, by omega⟩ (certE ⟨743, by omega⟩) := by
  have hm : certMode (⟨743, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨743, by omega⟩ : Fin 1104) = 203772941375493490267352770372 := by decide +kernel
  have he : certE (⟨743, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨743, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨743, by omega⟩ : Fin 1104)).2.2 = 21053911816 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_744 :
    ((certNum ⟨744, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨744, by omega⟩) ⟨744, by omega⟩ (certE ⟨744, by omega⟩) := by
  have hm : certMode (⟨744, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨744, by omega⟩ : Fin 1104) = 203947244958336424491245639882 := by decide +kernel
  have he : certE (⟨744, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨744, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨744, by omega⟩ : Fin 1104)).2.2 = 21076744234 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_745 :
    ((certNum ⟨745, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨745, by omega⟩) ⟨745, by omega⟩ (certE ⟨745, by omega⟩) := by
  have hm : certMode (⟨745, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨745, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨745, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨745, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨745, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_746 :
    ((certNum ⟨746, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨746, by omega⟩) ⟨746, by omega⟩ (certE ⟨746, by omega⟩) := by
  have hm : certMode (⟨746, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨746, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨746, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨746, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨746, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_747 :
    ((certNum ⟨747, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨747, by omega⟩) ⟨747, by omega⟩ (certE ⟨747, by omega⟩) := by
  have hm : certMode (⟨747, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨747, by omega⟩ : Fin 1104) = 203772501564451278772043390671 := by decide +kernel
  have he : certE (⟨747, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨747, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨747, by omega⟩ : Fin 1104)).2.2 = 21053854212 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_748 :
    ((certNum ⟨748, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨748, by omega⟩) ⟨748, by omega⟩ (certE ⟨748, by omega⟩) := by
  have hm : certMode (⟨748, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨748, by omega⟩ : Fin 1104) = 39827751866922906128321172265 := by decide +kernel
  have he : certE (⟨748, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then 6 else if j.val = 1 then 8 else if j.val = 2 then -2 else -8)) := by decide +kernel
  have hp : parent2 (⟨748, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨748, by omega⟩ : Fin 1104)).2.2 = 2913277513 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_749 :
    ((certNum ⟨749, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨749, by omega⟩) ⟨749, by omega⟩ (certE ⟨749, by omega⟩) := by
  have hm : certMode (⟨749, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨749, by omega⟩ : Fin 1104) = 203770989432200553855868141784 := by decide +kernel
  have he : certE (⟨749, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨749, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨749, by omega⟩ : Fin 1104)).2.2 = 21053656162 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_750 :
    ((certNum ⟨750, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨750, by omega⟩) ⟨750, by omega⟩ (certE ⟨750, by omega⟩) := by
  have hm : certMode (⟨750, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨750, by omega⟩ : Fin 1104) = 203947226265600660328212224431 := by decide +kernel
  have he : certE (⟨750, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨750, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨750, by omega⟩ : Fin 1104)).2.2 = 21076741785 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_751 :
    ((certNum ⟨751, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨751, by omega⟩) ⟨751, by omega⟩ (certE ⟨751, by omega⟩) := by
  have hm : certMode (⟨751, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨751, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨751, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨751, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨751, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_752 :
    ((certNum ⟨752, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨752, by omega⟩) ⟨752, by omega⟩ (certE ⟨752, by omega⟩) := by
  have hm : certMode (⟨752, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨752, by omega⟩ : Fin 1104) = 15884296405565733362754369080 := by decide +kernel
  have he : certE (⟨752, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -14 else if j.val = 1 then -6 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨752, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨752, by omega⟩ : Fin 1104)).2.2 = 1005127140 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_753 :
    ((certNum ⟨753, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨753, by omega⟩) ⟨753, by omega⟩ (certE ⟨753, by omega⟩) := by
  have hm : certMode (⟨753, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨753, by omega⟩ : Fin 1104) = 202780383058496760995504693066 := by decide +kernel
  have he : certE (⟨753, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨753, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨753, by omega⟩ : Fin 1104)).2.2 = 20924025542 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_754 :
    ((certNum ⟨754, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨754, by omega⟩) ⟨754, by omega⟩ (certE ⟨754, by omega⟩) := by
  have hm : certMode (⟨754, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨754, by omega⟩ : Fin 1104) = 15884563251194743959038811507 := by decide +kernel
  have he : certE (⟨754, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -14 else if j.val = 1 then -6 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨754, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨754, by omega⟩ : Fin 1104)).2.2 = 1005146475 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_755 :
    ((certNum ⟨755, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨755, by omega⟩) ⟨755, by omega⟩ (certE ⟨755, by omega⟩) := by
  have hm : certMode (⟨755, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨755, by omega⟩ : Fin 1104) = 202780510912280808329435727786 := by decide +kernel
  have he : certE (⟨755, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨755, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨755, by omega⟩ : Fin 1104)).2.2 = 20924042259 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_756 :
    ((certNum ⟨756, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨756, by omega⟩) ⟨756, by omega⟩ (certE ⟨756, by omega⟩) := by
  have hm : certMode (⟨756, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨756, by omega⟩ : Fin 1104) = 25548627472605782258890297666 := by decide +kernel
  have he : certE (⟨756, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -15 else if j.val = 1 then 3 else if j.val = 2 then -8 else 7)) := by decide +kernel
  have hp : parent2 (⟨756, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨756, by omega⟩ : Fin 1104)).2.2 = 1737104658 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_757 :
    ((certNum ⟨757, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨757, by omega⟩) ⟨757, by omega⟩ (certE ⟨757, by omega⟩) := by
  have hm : certMode (⟨757, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨757, by omega⟩ : Fin 1104) = 202780305330527455347043068071 := by decide +kernel
  have he : certE (⟨757, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨757, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨757, by omega⟩ : Fin 1104)).2.2 = 20924015379 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_758 :
    ((certNum ⟨758, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨758, by omega⟩) ⟨758, by omega⟩ (certE ⟨758, by omega⟩) := by
  have hm : certMode (⟨758, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨758, by omega⟩ : Fin 1104) = 203947278466340801954639874140 := by decide +kernel
  have he : certE (⟨758, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨758, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨758, by omega⟩ : Fin 1104)).2.2 = 21076748624 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_759 :
    ((certNum ⟨759, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨759, by omega⟩) ⟨759, by omega⟩ (certE ⟨759, by omega⟩) := by
  have hm : certMode (⟨759, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨759, by omega⟩ : Fin 1104) = 5022409646041905049848908661 := by decide +kernel
  have he : certE (⟨759, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -31 else if j.val = 1 then 8 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨759, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨759, by omega⟩ : Fin 1104)).2.2 = 272760131 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_760 :
    ((certNum ⟨760, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨760, by omega⟩) ⟨760, by omega⟩ (certE ⟨760, by omega⟩) := by
  have hm : certMode (⟨760, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨760, by omega⟩ : Fin 1104) = 203946899856200364670952112969 := by decide +kernel
  have he : certE (⟨760, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨760, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨760, by omega⟩ : Fin 1104)).2.2 = 21076699021 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_761 :
    ((certNum ⟨761, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨761, by omega⟩) ⟨761, by omega⟩ (certE ⟨761, by omega⟩) := by
  have hm : certMode (⟨761, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨761, by omega⟩ : Fin 1104) = 5022475938239351309079801792 := by decide +kernel
  have he : certE (⟨761, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -31 else if j.val = 1 then 8 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨761, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨761, by omega⟩ : Fin 1104)).2.2 = 272764170 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_762 :
    ((certNum ⟨762, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨762, by omega⟩) ⟨762, by omega⟩ (certE ⟨762, by omega⟩) := by
  have hm : certMode (⟨762, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨762, by omega⟩ : Fin 1104) = 203947342116272997552293254520 := by decide +kernel
  have he : certE (⟨762, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨762, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨762, by omega⟩ : Fin 1104)).2.2 = 21076756963 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_763 :
    ((certNum ⟨763, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨763, by omega⟩) ⟨763, by omega⟩ (certE ⟨763, by omega⟩) := by
  have hm : certMode (⟨763, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨763, by omega⟩ : Fin 1104) = 10496357414563682112037056655 := by decide +kernel
  have he : certE (⟨763, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -38 else if j.val = 1 then 2 else if j.val = 2 then 8 else 2)) := by decide +kernel
  have hp : parent2 (⟨763, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨763, by omega⟩ : Fin 1104)).2.2 = 626690999 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_764 :
    ((certNum ⟨764, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨764, by omega⟩) ⟨764, by omega⟩ (certE ⟨764, by omega⟩) := by
  have hm : certMode (⟨764, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨764, by omega⟩ : Fin 1104) = 203946116224857497963528182994 := by decide +kernel
  have he : certE (⟨764, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨764, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨764, by omega⟩ : Fin 1104)).2.2 = 21076596355 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_765 :
    ((certNum ⟨765, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨765, by omega⟩) ⟨765, by omega⟩ (certE ⟨765, by omega⟩) := by
  have hm : certMode (⟨765, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨765, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨765, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨765, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨765, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_766 :
    ((certNum ⟨766, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨766, by omega⟩) ⟨766, by omega⟩ (certE ⟨766, by omega⟩) := by
  have hm : certMode (⟨766, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨766, by omega⟩ : Fin 1104) = 203945881767046431127803894433 := by decide +kernel
  have he : certE (⟨766, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨766, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨766, by omega⟩ : Fin 1104)).2.2 = 21076565638 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_767 :
    ((certNum ⟨767, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨767, by omega⟩) ⟨767, by omega⟩ (certE ⟨767, by omega⟩) := by
  have hm : certMode (⟨767, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨767, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨767, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨767, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨767, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_768 :
    ((certNum ⟨768, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨768, by omega⟩) ⟨768, by omega⟩ (certE ⟨768, by omega⟩) := by
  have hm : certMode (⟨768, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨768, by omega⟩ : Fin 1104) = 203944928126272985402986100092 := by decide +kernel
  have he : certE (⟨768, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨768, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨768, by omega⟩ : Fin 1104)).2.2 = 21076440699 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_769 :
    ((certNum ⟨769, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨769, by omega⟩) ⟨769, by omega⟩ (certE ⟨769, by omega⟩) := by
  have hm : certMode (⟨769, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨769, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨769, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨769, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨769, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_770 :
    ((certNum ⟨770, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨770, by omega⟩) ⟨770, by omega⟩ (certE ⟨770, by omega⟩) := by
  have hm : certMode (⟨770, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨770, by omega⟩ : Fin 1104) = 30359316110668449279274192 := by decide +kernel
  have he : certE (⟨770, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -26 else if j.val = 1 then 3 else if j.val = 2 then 3 else -2)) := by decide +kernel
  have hp : parent2 (⟨770, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨770, by omega⟩ : Fin 1104)).2.2 = 1026383 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_771 :
    ((certNum ⟨771, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨771, by omega⟩) ⟨771, by omega⟩ (certE ⟨771, by omega⟩) := by
  have hm : certMode (⟨771, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨771, by omega⟩ : Fin 1104) = 30368472204583956196504371 := by decide +kernel
  have he : certE (⟨771, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -31 else if j.val = 1 then 2 else if j.val = 2 then 1 else 2)) := by decide +kernel
  have hp : parent2 (⟨771, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨771, by omega⟩ : Fin 1104)).2.2 = 1026715 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_772 :
    ((certNum ⟨772, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨772, by omega⟩) ⟨772, by omega⟩ (certE ⟨772, by omega⟩) := by
  have hm : certMode (⟨772, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨772, by omega⟩ : Fin 1104) = 30539006707428139676522114 := by decide +kernel
  have he : certE (⟨772, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -5 else if j.val = 1 then -2 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hp : parent2 (⟨772, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨772, by omega⟩ : Fin 1104)).2.2 = 1032900 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_773 :
    ((certNum ⟨773, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨773, by omega⟩) ⟨773, by omega⟩ (certE ⟨773, by omega⟩) := by
  have hm : certMode (⟨773, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨773, by omega⟩ : Fin 1104) = 30539089406628155053394599 := by decide +kernel
  have he : certE (⟨773, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -5 else if j.val = 1 then -2 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hp : parent2 (⟨773, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨773, by omega⟩ : Fin 1104)).2.2 = 1032903 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_774 :
    ((certNum ⟨774, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨774, by omega⟩) ⟨774, by omega⟩ (certE ⟨774, by omega⟩) := by
  have hm : certMode (⟨774, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨774, by omega⟩ : Fin 1104) = 30368444626165158512429192 := by decide +kernel
  have he : certE (⟨774, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -31 else if j.val = 1 then 2 else if j.val = 2 then 1 else 2)) := by decide +kernel
  have hp : parent2 (⟨774, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨774, by omega⟩ : Fin 1104)).2.2 = 1026714 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_775 :
    ((certNum ⟨775, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨775, by omega⟩) ⟨775, by omega⟩ (certE ⟨775, by omega⟩) := by
  have hm : certMode (⟨775, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨775, by omega⟩ : Fin 1104) = 30359233374018846829370561 := by decide +kernel
  have he : certE (⟨775, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -26 else if j.val = 1 then 3 else if j.val = 2 then 3 else -2)) := by decide +kernel
  have hp : parent2 (⟨775, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨775, by omega⟩ : Fin 1104)).2.2 = 1026380 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_776 :
    ((certNum ⟨776, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨776, by omega⟩) ⟨776, by omega⟩ (certE ⟨776, by omega⟩) := by
  have hm : certMode (⟨776, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨776, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨776, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨776, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨776, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_777 :
    ((certNum ⟨777, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨777, by omega⟩) ⟨777, by omega⟩ (certE ⟨777, by omega⟩) := by
  have hm : certMode (⟨777, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨777, by omega⟩ : Fin 1104) = 203878323957508830194547393596 := by decide +kernel
  have he : certE (⟨777, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨777, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨777, by omega⟩ : Fin 1104)).2.2 = 21067715289 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_778 :
    ((certNum ⟨778, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨778, by omega⟩) ⟨778, by omega⟩ (certE ⟨778, by omega⟩) := by
  have hm : certMode (⟨778, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨778, by omega⟩ : Fin 1104) = 39757164899625057442759678676 := by decide +kernel
  have he : certE (⟨778, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -12 else if j.val = 1 then -8 else if j.val = 2 then 7 else 0)) := by decide +kernel
  have hp : parent2 (⟨778, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨778, by omega⟩ : Fin 1104)).2.2 = 2907227530 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_779 :
    ((certNum ⟨779, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨779, by omega⟩) ⟨779, by omega⟩ (certE ⟨779, by omega⟩) := by
  have hm : certMode (⟨779, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨779, by omega⟩ : Fin 1104) = 203878535057332925142563332787 := by decide +kernel
  have he : certE (⟨779, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨779, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨779, by omega⟩ : Fin 1104)).2.2 = 21067742943 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_780 :
    ((certNum ⟨780, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨780, by omega⟩) ⟨780, by omega⟩ (certE ⟨780, by omega⟩) := by
  have hm : certMode (⟨780, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨780, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨780, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨780, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨780, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_781 :
    ((certNum ⟨781, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨781, by omega⟩) ⟨781, by omega⟩ (certE ⟨781, by omega⟩) := by
  have hm : certMode (⟨781, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨781, by omega⟩ : Fin 1104) = 203878070773398215109984971187 := by decide +kernel
  have he : certE (⟨781, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨781, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨781, by omega⟩ : Fin 1104)).2.2 = 21067682122 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_782 :
    ((certNum ⟨782, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨782, by omega⟩) ⟨782, by omega⟩ (certE ⟨782, by omega⟩) := by
  have hm : certMode (⟨782, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨782, by omega⟩ : Fin 1104) = 203947246065092894293826303295 := by decide +kernel
  have he : certE (⟨782, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨782, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨782, by omega⟩ : Fin 1104)).2.2 = 21076744379 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_783 :
    ((certNum ⟨783, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨783, by omega⟩) ⟨783, by omega⟩ (certE ⟨783, by omega⟩) := by
  have hm : certMode (⟨783, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨783, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨783, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨783, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨783, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_784 :
    ((certNum ⟨784, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨784, by omega⟩) ⟨784, by omega⟩ (certE ⟨784, by omega⟩) := by
  have hm : certMode (⟨784, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨784, by omega⟩ : Fin 1104) = 203947228547808969619269316492 := by decide +kernel
  have he : certE (⟨784, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨784, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨784, by omega⟩ : Fin 1104)).2.2 = 21076742084 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_785 :
    ((certNum ⟨785, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨785, by omega⟩) ⟨785, by omega⟩ (certE ⟨785, by omega⟩) := by
  have hm : certMode (⟨785, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨785, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨785, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨785, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨785, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_786 :
    ((certNum ⟨786, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨786, by omega⟩) ⟨786, by omega⟩ (certE ⟨786, by omega⟩) := by
  have hm : certMode (⟨786, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨786, by omega⟩ : Fin 1104) = 177418862645206320152670366080 := by decide +kernel
  have he : certE (⟨786, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then -30 else if j.val = 1 then 5 else if j.val = 2 then 7 else 0)) := by decide +kernel
  have hp : parent2 (⟨786, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨786, by omega⟩ : Fin 1104)).2.2 = 17680321551 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_787 :
    ((certNum ⟨787, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨787, by omega⟩) ⟨787, by omega⟩ (certE ⟨787, by omega⟩) := by
  have hm : certMode (⟨787, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨787, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨787, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨787, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨787, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_788 :
    ((certNum ⟨788, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨788, by omega⟩) ⟨788, by omega⟩ (certE ⟨788, by omega⟩) := by
  have hm : certMode (⟨788, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨788, by omega⟩ : Fin 1104) = 203878508003830994526151367224 := by decide +kernel
  have he : certE (⟨788, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨788, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨788, by omega⟩ : Fin 1104)).2.2 = 21067739399 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_789 :
    ((certNum ⟨789, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨789, by omega⟩) ⟨789, by omega⟩ (certE ⟨789, by omega⟩) := by
  have hm : certMode (⟨789, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨789, by omega⟩ : Fin 1104) = 177447262939361572385761018154 := by decide +kernel
  have he : certE (⟨789, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 17 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨789, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨789, by omega⟩ : Fin 1104)).2.2 = 17683872347 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_790 :
    ((certNum ⟨790, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨790, by omega⟩) ⟨790, by omega⟩ (certE ⟨790, by omega⟩) := by
  have hm : certMode (⟨790, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨790, by omega⟩ : Fin 1104) = 203774454948357432866702005990 := by decide +kernel
  have he : certE (⟨790, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨790, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨790, by omega⟩ : Fin 1104)).2.2 = 21054110056 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_791 :
    ((certNum ⟨791, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨791, by omega⟩) ⟨791, by omega⟩ (certE ⟨791, by omega⟩) := by
  have hm : certMode (⟨791, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨791, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨791, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨791, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨791, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_792 :
    ((certNum ⟨792, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨792, by omega⟩) ⟨792, by omega⟩ (certE ⟨792, by omega⟩) := by
  have hm : certMode (⟨792, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨792, by omega⟩ : Fin 1104) = 203947295960723346910953578354 := by decide +kernel
  have he : certE (⟨792, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨792, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨792, by omega⟩ : Fin 1104)).2.2 = 21076750916 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_793 :
    ((certNum ⟨793, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨793, by omega⟩) ⟨793, by omega⟩ (certE ⟨793, by omega⟩) := by
  have hm : certMode (⟨793, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨793, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨793, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨793, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨793, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_794 :
    ((certNum ⟨794, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨794, by omega⟩) ⟨794, by omega⟩ (certE ⟨794, by omega⟩) := by
  have hm : certMode (⟨794, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨794, by omega⟩ : Fin 1104) = 3072504285788597047678912 := by decide +kernel
  have he : certE (⟨794, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -40 else if j.val = 1 then 6 else if j.val = 2 then -3 else 5)) := by decide +kernel
  have hp : parent2 (⟨794, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨794, by omega⟩ : Fin 1104)).2.2 = 89146 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_795 :
    ((certNum ⟨795, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨795, by omega⟩) ⟨795, by omega⟩ (certE ⟨795, by omega⟩) := by
  have hm : certMode (⟨795, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨795, by omega⟩ : Fin 1104) = 203947296243137018200793213066 := by decide +kernel
  have he : certE (⟨795, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨795, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨795, by omega⟩ : Fin 1104)).2.2 = 21076750953 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_796 :
    ((certNum ⟨796, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨796, by omega⟩) ⟨796, by omega⟩ (certE ⟨796, by omega⟩) := by
  have hm : certMode (⟨796, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨796, by omega⟩ : Fin 1104) = 3000048894902136166879727 := by decide +kernel
  have he : certE (⟨796, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -27 else if j.val = 1 then -1 else if j.val = 2 then 1 else 1)) := by decide +kernel
  have hp : parent2 (⟨796, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨796, by omega⟩ : Fin 1104)).2.2 = 86916 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_797 :
    ((certNum ⟨797, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨797, by omega⟩) ⟨797, by omega⟩ (certE ⟨797, by omega⟩) := by
  have hm : certMode (⟨797, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨797, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨797, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨797, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨797, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_798 :
    ((certNum ⟨798, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨798, by omega⟩) ⟨798, by omega⟩ (certE ⟨798, by omega⟩) := by
  have hm : certMode (⟨798, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨798, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨798, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨798, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨798, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_799 :
    ((certNum ⟨799, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨799, by omega⟩) ⟨799, by omega⟩ (certE ⟨799, by omega⟩) := by
  have hm : certMode (⟨799, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨799, by omega⟩ : Fin 1104) = 202780313169864072010654804521 := by decide +kernel
  have he : certE (⟨799, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨799, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨799, by omega⟩ : Fin 1104)).2.2 = 20924016404 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_800 :
    ((certNum ⟨800, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨800, by omega⟩) ⟨800, by omega⟩ (certE ⟨800, by omega⟩) := by
  have hm : certMode (⟨800, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨800, by omega⟩ : Fin 1104) = 190637442936707867170115894918 := by decide +kernel
  have he : certE (⟨800, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨800, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨800, by omega⟩ : Fin 1104)).2.2 = 19352843007 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_801 :
    ((certNum ⟨801, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨801, by omega⟩) ⟨801, by omega⟩ (certE ⟨801, by omega⟩) := by
  have hm : certMode (⟨801, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨801, by omega⟩ : Fin 1104) = 91614813890035449103302295641 := by decide +kernel
  have he : certE (⟨801, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -6 else if j.val = 1 then -1 else if j.val = 2 then -7 else 6)) := by decide +kernel
  have hp : parent2 (⟨801, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨801, by omega⟩ : Fin 1104)).2.2 = 7843482348 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_802 :
    ((certNum ⟨802, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨802, by omega⟩) ⟨802, by omega⟩ (certE ⟨802, by omega⟩) := by
  have hm : certMode (⟨802, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨802, by omega⟩ : Fin 1104) = 202780327280669453728429685634 := by decide +kernel
  have he : certE (⟨802, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨802, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨802, by omega⟩ : Fin 1104)).2.2 = 20924018249 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_803 :
    ((certNum ⟨803, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨803, by omega⟩) ⟨803, by omega⟩ (certE ⟨803, by omega⟩) := by
  have hm : certMode (⟨803, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨803, by omega⟩ : Fin 1104) = 180942031974436378226428517517 := by decide +kernel
  have he : certE (⟨803, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 14 else if j.val = 1 then -4 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨803, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨803, by omega⟩ : Fin 1104)).2.2 = 18122214681 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_804 :
    ((certNum ⟨804, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨804, by omega⟩) ⟨804, by omega⟩ (certE ⟨804, by omega⟩) := by
  have hm : certMode (⟨804, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨804, by omega⟩ : Fin 1104) = 203947315546492448054628903226 := by decide +kernel
  have he : certE (⟨804, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨804, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨804, by omega⟩ : Fin 1104)).2.2 = 21076753482 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_805 :
    ((certNum ⟨805, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨805, by omega⟩) ⟨805, by omega⟩ (certE ⟨805, by omega⟩) := by
  have hm : certMode (⟨805, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨805, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨805, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨805, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨805, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_806 :
    ((certNum ⟨806, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨806, by omega⟩) ⟨806, by omega⟩ (certE ⟨806, by omega⟩) := by
  have hm : certMode (⟨806, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨806, by omega⟩ : Fin 1104) = 190768544736798276444441962682 := by decide +kernel
  have he : certE (⟨806, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨806, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨806, by omega⟩ : Fin 1104)).2.2 = 19369629463 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_807 :
    ((certNum ⟨807, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨807, by omega⟩) ⟨807, by omega⟩ (certE ⟨807, by omega⟩) := by
  have hm : certMode (⟨807, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨807, by omega⟩ : Fin 1104) = 203947313951236946530576584289 := by decide +kernel
  have he : certE (⟨807, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨807, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨807, by omega⟩ : Fin 1104)).2.2 = 21076753273 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_808 :
    ((certNum ⟨808, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨808, by omega⟩) ⟨808, by omega⟩ (certE ⟨808, by omega⟩) := by
  have hm : certMode (⟨808, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨808, by omega⟩ : Fin 1104) = 89091404983737541585123402927 := by decide +kernel
  have he : certE (⟨808, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -8 else -1)) := by decide +kernel
  have hp : parent2 (⟨808, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨808, by omega⟩ : Fin 1104)).2.2 = 7583299349 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_809 :
    ((certNum ⟨809, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨809, by omega⟩) ⟨809, by omega⟩ (certE ⟨809, by omega⟩) := by
  have hm : certMode (⟨809, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨809, by omega⟩ : Fin 1104) = 181441350392169016658279727029 := by decide +kernel
  have he : certE (⟨809, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hp : parent2 (⟨809, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨809, by omega⟩ : Fin 1104)).2.2 = 18185070892 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_810 :
    ((certNum ⟨810, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨810, by omega⟩) ⟨810, by omega⟩ (certE ⟨810, by omega⟩) := by
  have hm : certMode (⟨810, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨810, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨810, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨810, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨810, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_811 :
    ((certNum ⟨811, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨811, by omega⟩) ⟨811, by omega⟩ (certE ⟨811, by omega⟩) := by
  have hm : certMode (⟨811, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨811, by omega⟩ : Fin 1104) = 154742426545703381200987228569 := by decide +kernel
  have he : certE (⟨811, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then 27 else if j.val = 1 then -7 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨811, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨811, by omega⟩ : Fin 1104)).2.2 = 14904835381 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_812 :
    ((certNum ⟨812, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨812, by omega⟩) ⟨812, by omega⟩ (certE ⟨812, by omega⟩) := by
  have hm : certMode (⟨812, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨812, by omega⟩ : Fin 1104) = 203877557938836842376481390470 := by decide +kernel
  have he : certE (⟨812, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨812, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨812, by omega⟩ : Fin 1104)).2.2 = 21067614941 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_813 :
    ((certNum ⟨813, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨813, by omega⟩) ⟨813, by omega⟩ (certE ⟨813, by omega⟩) := by
  have hm : certMode (⟨813, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨813, by omega⟩ : Fin 1104) = 204039918537767178815903853117 := by decide +kernel
  have he : certE (⟨813, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨813, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨813, by omega⟩ : Fin 1104)).2.2 = 21088886636 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_814 :
    ((certNum ⟨814, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨814, by omega⟩) ⟨814, by omega⟩ (certE ⟨814, by omega⟩) := by
  have hm : certMode (⟨814, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨814, by omega⟩ : Fin 1104) = 23254227871559157043236600944 := by decide +kernel
  have he : certE (⟨814, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (37 : Int) else if j.val = 1 then -1 else if j.val = 2 then -8 else -6) else (if j.val = 0 then -19 else if j.val = 1 then -8 else if j.val = 2 then 6 else 3)) := by decide +kernel
  have hp : parent2 (⟨814, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨814, by omega⟩ : Fin 1104)).2.2 = 1558012833 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_815 :
    ((certNum ⟨815, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨815, by omega⟩) ⟨815, by omega⟩ (certE ⟨815, by omega⟩) := by
  have hm : certMode (⟨815, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨815, by omega⟩ : Fin 1104) = 203878644088111320810891965779 := by decide +kernel
  have he : certE (⟨815, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨815, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨815, by omega⟩ : Fin 1104)).2.2 = 21067757226 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_816 :
    ((certNum ⟨816, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨816, by omega⟩) ⟨816, by omega⟩ (certE ⟨816, by omega⟩) := by
  have hm : certMode (⟨816, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨816, by omega⟩ : Fin 1104) = 203947332697396743070718508112 := by decide +kernel
  have he : certE (⟨816, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨816, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨816, by omega⟩ : Fin 1104)).2.2 = 21076755729 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_817 :
    ((certNum ⟨817, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨817, by omega⟩) ⟨817, by omega⟩ (certE ⟨817, by omega⟩) := by
  have hm : certMode (⟨817, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨817, by omega⟩ : Fin 1104) = 23256006988460045234819732613 := by decide +kernel
  have he : certE (⟨817, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (37 : Int) else if j.val = 1 then -1 else if j.val = 2 then -8 else -6) else (if j.val = 0 then -19 else if j.val = 1 then -8 else if j.val = 2 then 6 else 3)) := by decide +kernel
  have hp : parent2 (⟨817, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨817, by omega⟩ : Fin 1104)).2.2 = 1558150511 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_818 :
    ((certNum ⟨818, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨818, by omega⟩) ⟨818, by omega⟩ (certE ⟨818, by omega⟩) := by
  have hm : certMode (⟨818, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨818, by omega⟩ : Fin 1104) = 203971023058216876955853028527 := by decide +kernel
  have he : certE (⟨818, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then -6 else if j.val = 2 then -4 else 4)) := by decide +kernel
  have hp : parent2 (⟨818, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨818, by omega⟩ : Fin 1104)).2.2 = 21079859535 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_819 :
    ((certNum ⟨819, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨819, by omega⟩) ⟨819, by omega⟩ (certE ⟨819, by omega⟩) := by
  have hm : certMode (⟨819, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨819, by omega⟩ : Fin 1104) = 203946765167565208466898401079 := by decide +kernel
  have he : certE (⟨819, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨819, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨819, by omega⟩ : Fin 1104)).2.2 = 21076681375 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_820 :
    ((certNum ⟨820, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨820, by omega⟩) ⟨820, by omega⟩ (certE ⟨820, by omega⟩) := by
  have hm : certMode (⟨820, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨820, by omega⟩ : Fin 1104) = 154723232299766305839793687868 := by decide +kernel
  have he : certE (⟨820, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -20 else if j.val = 1 then 0 else if j.val = 2 then 6 else 0)) := by decide +kernel
  have hp : parent2 (⟨820, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨820, by omega⟩ : Fin 1104)).2.2 = 14902537119 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_821 :
    ((certNum ⟨821, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨821, by omega⟩) ⟨821, by omega⟩ (certE ⟨821, by omega⟩) := by
  have hm : certMode (⟨821, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨821, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨821, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨821, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨821, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_822 :
    ((certNum ⟨822, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨822, by omega⟩) ⟨822, by omega⟩ (certE ⟨822, by omega⟩) := by
  have hm : certMode (⟨822, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨822, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨822, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨822, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨822, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_823 :
    ((certNum ⟨823, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨823, by omega⟩) ⟨823, by omega⟩ (certE ⟨823, by omega⟩) := by
  have hm : certMode (⟨823, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨823, by omega⟩ : Fin 1104) = 203878777851714262778788507702 := by decide +kernel
  have he : certE (⟨823, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨823, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨823, by omega⟩ : Fin 1104)).2.2 = 21067774749 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_824 :
    ((certNum ⟨824, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨824, by omega⟩) ⟨824, by omega⟩ (certE ⟨824, by omega⟩) := by
  have hm : certMode (⟨824, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨824, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨824, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨824, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨824, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_825 :
    ((certNum ⟨825, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨825, by omega⟩) ⟨825, by omega⟩ (certE ⟨825, by omega⟩) := by
  have hm : certMode (⟨825, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨825, by omega⟩ : Fin 1104) = 203878064116882942928117899734 := by decide +kernel
  have he : certE (⟨825, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨825, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨825, by omega⟩ : Fin 1104)).2.2 = 21067681250 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_826 :
    ((certNum ⟨826, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨826, by omega⟩) ⟨826, by omega⟩ (certE ⟨826, by omega⟩) := by
  have hm : certMode (⟨826, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨826, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨826, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨826, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨826, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_827 :
    ((certNum ⟨827, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨827, by omega⟩) ⟨827, by omega⟩ (certE ⟨827, by omega⟩) := by
  have hm : certMode (⟨827, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨827, by omega⟩ : Fin 1104) = 203877848917464536024344223070 := by decide +kernel
  have he : certE (⟨827, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨827, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨827, by omega⟩ : Fin 1104)).2.2 = 21067653059 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨736 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨736 + j.val, by omega⟩) ⟨736 + j.val, by omega⟩
        (certE ⟨736 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_736
  | ⟨1, _⟩ => exact MME.L2Cert.cert_737
  | ⟨2, _⟩ => exact MME.L2Cert.cert_738
  | ⟨3, _⟩ => exact MME.L2Cert.cert_739
  | ⟨4, _⟩ => exact MME.L2Cert.cert_740
  | ⟨5, _⟩ => exact MME.L2Cert.cert_741
  | ⟨6, _⟩ => exact MME.L2Cert.cert_742
  | ⟨7, _⟩ => exact MME.L2Cert.cert_743
  | ⟨8, _⟩ => exact MME.L2Cert.cert_744
  | ⟨9, _⟩ => exact MME.L2Cert.cert_745
  | ⟨10, _⟩ => exact MME.L2Cert.cert_746
  | ⟨11, _⟩ => exact MME.L2Cert.cert_747
  | ⟨12, _⟩ => exact MME.L2Cert.cert_748
  | ⟨13, _⟩ => exact MME.L2Cert.cert_749
  | ⟨14, _⟩ => exact MME.L2Cert.cert_750
  | ⟨15, _⟩ => exact MME.L2Cert.cert_751
  | ⟨16, _⟩ => exact MME.L2Cert.cert_752
  | ⟨17, _⟩ => exact MME.L2Cert.cert_753
  | ⟨18, _⟩ => exact MME.L2Cert.cert_754
  | ⟨19, _⟩ => exact MME.L2Cert.cert_755
  | ⟨20, _⟩ => exact MME.L2Cert.cert_756
  | ⟨21, _⟩ => exact MME.L2Cert.cert_757
  | ⟨22, _⟩ => exact MME.L2Cert.cert_758
  | ⟨23, _⟩ => exact MME.L2Cert.cert_759
  | ⟨24, _⟩ => exact MME.L2Cert.cert_760
  | ⟨25, _⟩ => exact MME.L2Cert.cert_761
  | ⟨26, _⟩ => exact MME.L2Cert.cert_762
  | ⟨27, _⟩ => exact MME.L2Cert.cert_763
  | ⟨28, _⟩ => exact MME.L2Cert.cert_764
  | ⟨29, _⟩ => exact MME.L2Cert.cert_765
  | ⟨30, _⟩ => exact MME.L2Cert.cert_766
  | ⟨31, _⟩ => exact MME.L2Cert.cert_767
  | ⟨32, _⟩ => exact MME.L2Cert.cert_768
  | ⟨33, _⟩ => exact MME.L2Cert.cert_769
  | ⟨34, _⟩ => exact MME.L2Cert.cert_770
  | ⟨35, _⟩ => exact MME.L2Cert.cert_771
  | ⟨36, _⟩ => exact MME.L2Cert.cert_772
  | ⟨37, _⟩ => exact MME.L2Cert.cert_773
  | ⟨38, _⟩ => exact MME.L2Cert.cert_774
  | ⟨39, _⟩ => exact MME.L2Cert.cert_775
  | ⟨40, _⟩ => exact MME.L2Cert.cert_776
  | ⟨41, _⟩ => exact MME.L2Cert.cert_777
  | ⟨42, _⟩ => exact MME.L2Cert.cert_778
  | ⟨43, _⟩ => exact MME.L2Cert.cert_779
  | ⟨44, _⟩ => exact MME.L2Cert.cert_780
  | ⟨45, _⟩ => exact MME.L2Cert.cert_781
  | ⟨46, _⟩ => exact MME.L2Cert.cert_782
  | ⟨47, _⟩ => exact MME.L2Cert.cert_783
  | ⟨48, _⟩ => exact MME.L2Cert.cert_784
  | ⟨49, _⟩ => exact MME.L2Cert.cert_785
  | ⟨50, _⟩ => exact MME.L2Cert.cert_786
  | ⟨51, _⟩ => exact MME.L2Cert.cert_787
  | ⟨52, _⟩ => exact MME.L2Cert.cert_788
  | ⟨53, _⟩ => exact MME.L2Cert.cert_789
  | ⟨54, _⟩ => exact MME.L2Cert.cert_790
  | ⟨55, _⟩ => exact MME.L2Cert.cert_791
  | ⟨56, _⟩ => exact MME.L2Cert.cert_792
  | ⟨57, _⟩ => exact MME.L2Cert.cert_793
  | ⟨58, _⟩ => exact MME.L2Cert.cert_794
  | ⟨59, _⟩ => exact MME.L2Cert.cert_795
  | ⟨60, _⟩ => exact MME.L2Cert.cert_796
  | ⟨61, _⟩ => exact MME.L2Cert.cert_797
  | ⟨62, _⟩ => exact MME.L2Cert.cert_798
  | ⟨63, _⟩ => exact MME.L2Cert.cert_799
  | ⟨64, _⟩ => exact MME.L2Cert.cert_800
  | ⟨65, _⟩ => exact MME.L2Cert.cert_801
  | ⟨66, _⟩ => exact MME.L2Cert.cert_802
  | ⟨67, _⟩ => exact MME.L2Cert.cert_803
  | ⟨68, _⟩ => exact MME.L2Cert.cert_804
  | ⟨69, _⟩ => exact MME.L2Cert.cert_805
  | ⟨70, _⟩ => exact MME.L2Cert.cert_806
  | ⟨71, _⟩ => exact MME.L2Cert.cert_807
  | ⟨72, _⟩ => exact MME.L2Cert.cert_808
  | ⟨73, _⟩ => exact MME.L2Cert.cert_809
  | ⟨74, _⟩ => exact MME.L2Cert.cert_810
  | ⟨75, _⟩ => exact MME.L2Cert.cert_811
  | ⟨76, _⟩ => exact MME.L2Cert.cert_812
  | ⟨77, _⟩ => exact MME.L2Cert.cert_813
  | ⟨78, _⟩ => exact MME.L2Cert.cert_814
  | ⟨79, _⟩ => exact MME.L2Cert.cert_815
  | ⟨80, _⟩ => exact MME.L2Cert.cert_816
  | ⟨81, _⟩ => exact MME.L2Cert.cert_817
  | ⟨82, _⟩ => exact MME.L2Cert.cert_818
  | ⟨83, _⟩ => exact MME.L2Cert.cert_819
  | ⟨84, _⟩ => exact MME.L2Cert.cert_820
  | ⟨85, _⟩ => exact MME.L2Cert.cert_821
  | ⟨86, _⟩ => exact MME.L2Cert.cert_822
  | ⟨87, _⟩ => exact MME.L2Cert.cert_823
  | ⟨88, _⟩ => exact MME.L2Cert.cert_824
  | ⟨89, _⟩ => exact MME.L2Cert.cert_825
  | ⟨90, _⟩ => exact MME.L2Cert.cert_826
  | ⟨91, _⟩ => exact MME.L2Cert.cert_827
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
