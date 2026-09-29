-- Prove2me | solution 1 for mme_released_recursive_level2_cert11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T01:10:12.338901+00:00
-- url     : https://prove2.me/submissions/ca77d4ed-8044-4965-8beb-83e1c3a61930

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

theorem cert_1012 :
    ((certNum ⟨1012, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1012, by omega⟩) ⟨1012, by omega⟩ (certE ⟨1012, by omega⟩) := by
  have hm : certMode (⟨1012, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1012, by omega⟩ : Fin 1104) = 203866107321769622559178765142 := by decide +kernel
  have he : certE (⟨1012, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1012, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1012, by omega⟩ : Fin 1104)).2.2 = 21066114948 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1013 :
    ((certNum ⟨1013, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1013, by omega⟩) ⟨1013, by omega⟩ (certE ⟨1013, by omega⟩) := by
  have hm : certMode (⟨1013, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1013, by omega⟩ : Fin 1104) = 203947211999890124902757664035 := by decide +kernel
  have he : certE (⟨1013, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1013, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1013, by omega⟩ : Fin 1104)).2.2 = 21076739916 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1014 :
    ((certNum ⟨1014, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1014, by omega⟩) ⟨1014, by omega⟩ (certE ⟨1014, by omega⟩) := by
  have hm : certMode (⟨1014, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1014, by omega⟩ : Fin 1104) = 169595108607545162790577134707 := by decide +kernel
  have he : certE (⟨1014, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then -33 else if j.val = 1 then 8 else if j.val = 2 then 5 else 1)) := by decide +kernel
  have hp : parent2 (⟨1014, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1014, by omega⟩ : Fin 1104)).2.2 = 16709219779 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1015 :
    ((certNum ⟨1015, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1015, by omega⟩) ⟨1015, by omega⟩ (certE ⟨1015, by omega⟩) := by
  have hm : certMode (⟨1015, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1015, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1015, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1015, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1015, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1016 :
    ((certNum ⟨1016, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1016, by omega⟩) ⟨1016, by omega⟩ (certE ⟨1016, by omega⟩) := by
  have hm : certMode (⟨1016, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1016, by omega⟩ : Fin 1104) = 157462939391832067816282306 := by decide +kernel
  have he : certE (⟨1016, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -5 else if j.val = 1 then -4 else if j.val = 2 then -5 else 2)) := by decide +kernel
  have hp : parent2 (⟨1016, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1016, by omega⟩ : Fin 1104)).2.2 = 6049006 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1017 :
    ((certNum ⟨1017, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1017, by omega⟩) ⟨1017, by omega⟩ (certE ⟨1017, by omega⟩) := by
  have hm : certMode (⟨1017, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1017, by omega⟩ : Fin 1104) = 203778783439058365181330631083 := by decide +kernel
  have he : certE (⟨1017, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨1017, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1017, by omega⟩ : Fin 1104)).2.2 = 21054676971 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1018 :
    ((certNum ⟨1018, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1018, by omega⟩) ⟨1018, by omega⟩ (certE ⟨1018, by omega⟩) := by
  have hm : certMode (⟨1018, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1018, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1018, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1018, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1018, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1019 :
    ((certNum ⟨1019, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1019, by omega⟩) ⟨1019, by omega⟩ (certE ⟨1019, by omega⟩) := by
  have hm : certMode (⟨1019, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1019, by omega⟩ : Fin 1104) = 203776410014246224963679229624 := by decide +kernel
  have he : certE (⟨1019, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨1019, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1019, by omega⟩ : Fin 1104)).2.2 = 21054366122 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1020 :
    ((certNum ⟨1020, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1020, by omega⟩) ⟨1020, by omega⟩ (certE ⟨1020, by omega⟩) := by
  have hm : certMode (⟨1020, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1020, by omega⟩ : Fin 1104) = 180607131648099503122122571827 := by decide +kernel
  have he : certE (⟨1020, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨1020, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1020, by omega⟩ : Fin 1104)).2.2 = 18080087794 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1021 :
    ((certNum ⟨1021, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1021, by omega⟩) ⟨1021, by omega⟩ (certE ⟨1021, by omega⟩) := by
  have hm : certMode (⟨1021, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1021, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1021, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1021, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1021, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1022 :
    ((certNum ⟨1022, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1022, by omega⟩) ⟨1022, by omega⟩ (certE ⟨1022, by omega⟩) := by
  have hm : certMode (⟨1022, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1022, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1022, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1022, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1022, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1023 :
    ((certNum ⟨1023, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1023, by omega⟩) ⟨1023, by omega⟩ (certE ⟨1023, by omega⟩) := by
  have hm : certMode (⟨1023, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1023, by omega⟩ : Fin 1104) = 203775849537293771673163778570 := by decide +kernel
  have he : certE (⟨1023, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨1023, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1023, by omega⟩ : Fin 1104)).2.2 = 21054292713 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1024 :
    ((certNum ⟨1024, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1024, by omega⟩) ⟨1024, by omega⟩ (certE ⟨1024, by omega⟩) := by
  have hm : certMode (⟨1024, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1024, by omega⟩ : Fin 1104) = 180600640337999184512102696396 := by decide +kernel
  have he : certE (⟨1024, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨1024, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1024, by omega⟩ : Fin 1104)).2.2 = 18079271509 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1025 :
    ((certNum ⟨1025, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1025, by omega⟩) ⟨1025, by omega⟩ (certE ⟨1025, by omega⟩) := by
  have hm : certMode (⟨1025, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1025, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1025, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1025, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1025, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1026 :
    ((certNum ⟨1026, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1026, by omega⟩) ⟨1026, by omega⟩ (certE ⟨1026, by omega⟩) := by
  have hm : certMode (⟨1026, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1026, by omega⟩ : Fin 1104) = 15886109482930105412175786776 := by decide +kernel
  have he : certE (⟨1026, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -18 else if j.val = 1 then 0 else if j.val = 2 then -5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1026, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1026, by omega⟩ : Fin 1104)).2.2 = 1005258512 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1027 :
    ((certNum ⟨1027, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1027, by omega⟩) ⟨1027, by omega⟩ (certE ⟨1027, by omega⟩) := by
  have hm : certMode (⟨1027, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1027, by omega⟩ : Fin 1104) = 202773208197485003966770073305 := by decide +kernel
  have he : certE (⟨1027, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1027, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1027, by omega⟩ : Fin 1104)).2.2 = 20923087434 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1028 :
    ((certNum ⟨1028, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1028, by omega⟩) ⟨1028, by omega⟩ (certE ⟨1028, by omega⟩) := by
  have hm : certMode (⟨1028, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1028, by omega⟩ : Fin 1104) = 25552845218372767081417108035 := by decide +kernel
  have he : certE (⟨1028, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -16 else if j.val = 1 then 7 else if j.val = 2 then 3 else -4)) := by decide +kernel
  have hp : parent2 (⟨1028, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1028, by omega⟩ : Fin 1104)).2.2 = 1737436660 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1029 :
    ((certNum ⟨1029, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1029, by omega⟩) ⟨1029, by omega⟩ (certE ⟨1029, by omega⟩) := by
  have hm : certMode (⟨1029, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1029, by omega⟩ : Fin 1104) = 202773012637562983954914483116 := by decide +kernel
  have he : certE (⟨1029, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1029, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1029, by omega⟩ : Fin 1104)).2.2 = 20923061865 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1030 :
    ((certNum ⟨1030, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1030, by omega⟩) ⟨1030, by omega⟩ (certE ⟨1030, by omega⟩) := by
  have hm : certMode (⟨1030, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1030, by omega⟩ : Fin 1104) = 15886555379330684535277776198 := by decide +kernel
  have he : certE (⟨1030, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -18 else if j.val = 1 then 0 else if j.val = 2 then -5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1030, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1030, by omega⟩ : Fin 1104)).2.2 = 1005290821 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1031 :
    ((certNum ⟨1031, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1031, by omega⟩) ⟨1031, by omega⟩ (certE ⟨1031, by omega⟩) := by
  have hm : certMode (⟨1031, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1031, by omega⟩ : Fin 1104) = 202773103843808247180874120900 := by decide +kernel
  have he : certE (⟨1031, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1031, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1031, by omega⟩ : Fin 1104)).2.2 = 20923073790 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1032 :
    ((certNum ⟨1032, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1032, by omega⟩) ⟨1032, by omega⟩ (certE ⟨1032, by omega⟩) := by
  have hm : certMode (⟨1032, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1032, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1032, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1032, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1032, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1033 :
    ((certNum ⟨1033, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1033, by omega⟩) ⟨1033, by omega⟩ (certE ⟨1033, by omega⟩) := by
  have hm : certMode (⟨1033, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1033, by omega⟩ : Fin 1104) = 190640270819219339985258935700 := by decide +kernel
  have he : certE (⟨1033, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨1033, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1033, by omega⟩ : Fin 1104)).2.2 = 19353205050 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1034 :
    ((certNum ⟨1034, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1034, by omega⟩) ⟨1034, by omega⟩ (certE ⟨1034, by omega⟩) := by
  have hm : certMode (⟨1034, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1034, by omega⟩ : Fin 1104) = 202772974250624103327152713395 := by decide +kernel
  have he : certE (⟨1034, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1034, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1034, by omega⟩ : Fin 1104)).2.2 = 20923056846 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1035 :
    ((certNum ⟨1035, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1035, by omega⟩) ⟨1035, by omega⟩ (certE ⟨1035, by omega⟩) := by
  have hm : certMode (⟨1035, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1035, by omega⟩ : Fin 1104) = 91626088363668223338126850414 := by decide +kernel
  have he : certE (⟨1035, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -7 else if j.val = 1 then -8 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hp : parent2 (⟨1035, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1035, by omega⟩ : Fin 1104)).2.2 = 7844648967 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1036 :
    ((certNum ⟨1036, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1036, by omega⟩) ⟨1036, by omega⟩ (certE ⟨1036, by omega⟩) := by
  have hm : certMode (⟨1036, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1036, by omega⟩ : Fin 1104) = 180943776192734568389409386343 := by decide +kernel
  have he : certE (⟨1036, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 14 else if j.val = 1 then -4 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨1036, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1036, by omega⟩ : Fin 1104)).2.2 = 18122434145 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1037 :
    ((certNum ⟨1037, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1037, by omega⟩) ⟨1037, by omega⟩ (certE ⟨1037, by omega⟩) := by
  have hm : certMode (⟨1037, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1037, by omega⟩ : Fin 1104) = 202772965837466872996565336811 := by decide +kernel
  have he : certE (⟨1037, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1037, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1037, by omega⟩ : Fin 1104)).2.2 = 20923055746 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1038 :
    ((certNum ⟨1038, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1038, by omega⟩) ⟨1038, by omega⟩ (certE ⟨1038, by omega⟩) := by
  have hm : certMode (⟨1038, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1038, by omega⟩ : Fin 1104) = 203947313706987299600190474392 := by decide +kernel
  have he : certE (⟨1038, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1038, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1038, by omega⟩ : Fin 1104)).2.2 = 21076753241 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1039 :
    ((certNum ⟨1039, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1039, by omega⟩) ⟨1039, by omega⟩ (certE ⟨1039, by omega⟩) := by
  have hm : certMode (⟨1039, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1039, by omega⟩ : Fin 1104) = 181444879513254655080390833244 := by decide +kernel
  have he : certE (⟨1039, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hp : parent2 (⟨1039, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1039, by omega⟩ : Fin 1104)).2.2 = 18185515349 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1040 :
    ((certNum ⟨1040, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1040, by omega⟩) ⟨1040, by omega⟩ (certE ⟨1040, by omega⟩) := by
  have hm : certMode (⟨1040, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1040, by omega⟩ : Fin 1104) = 89071964814430681141120479829 := by decide +kernel
  have he : certE (⟨1040, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 16 else if j.val = 1 then -8 else if j.val = 2 then 4 else -7)) := by decide +kernel
  have hp : parent2 (⟨1040, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1040, by omega⟩ : Fin 1104)).2.2 = 7581302095 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1041 :
    ((certNum ⟨1041, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1041, by omega⟩) ⟨1041, by omega⟩ (certE ⟨1041, by omega⟩) := by
  have hm : certMode (⟨1041, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1041, by omega⟩ : Fin 1104) = 203947315470164433824789071472 := by decide +kernel
  have he : certE (⟨1041, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1041, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1041, by omega⟩ : Fin 1104)).2.2 = 21076753472 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1042 :
    ((certNum ⟨1042, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1042, by omega⟩) ⟨1042, by omega⟩ (certE ⟨1042, by omega⟩) := by
  have hm : certMode (⟨1042, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1042, by omega⟩ : Fin 1104) = 190769316950624106164839309206 := by decide +kernel
  have he : certE (⟨1042, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨1042, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1042, by omega⟩ : Fin 1104)).2.2 = 19369728352 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1043 :
    ((certNum ⟨1043, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1043, by omega⟩) ⟨1043, by omega⟩ (certE ⟨1043, by omega⟩) := by
  have hm : certMode (⟨1043, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1043, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1043, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1043, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1043, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1044 :
    ((certNum ⟨1044, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1044, by omega⟩) ⟨1044, by omega⟩ (certE ⟨1044, by omega⟩) := by
  have hm : certMode (⟨1044, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1044, by omega⟩ : Fin 1104) = 181358714083381623100558478865 := by decide +kernel
  have he : certE (⟨1044, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then -3 else 6)) := by decide +kernel
  have hp : parent2 (⟨1044, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1044, by omega⟩ : Fin 1104)).2.2 = 18174664478 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1045 :
    ((certNum ⟨1045, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1045, by omega⟩) ⟨1045, by omega⟩ (certE ⟨1045, by omega⟩) := by
  have hm : certMode (⟨1045, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1045, by omega⟩ : Fin 1104) = 90559263484440013844340850097 := by decide +kernel
  have he : certE (⟨1045, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then 14 else if j.val = 1 then 5 else if j.val = 2 then -4 else -7)) := by decide +kernel
  have hp : parent2 (⟨1045, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1045, by omega⟩ : Fin 1104)).2.2 = 7734423231 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1046 :
    ((certNum ⟨1046, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1046, by omega⟩) ⟨1046, by omega⟩ (certE ⟨1046, by omega⟩) := by
  have hm : certMode (⟨1046, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1046, by omega⟩ : Fin 1104) = 202772962319237414175221772498 := by decide +kernel
  have he : certE (⟨1046, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1046, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1046, by omega⟩ : Fin 1104)).2.2 = 20923055286 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1047 :
    ((certNum ⟨1047, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1047, by omega⟩) ⟨1047, by omega⟩ (certE ⟨1047, by omega⟩) := by
  have hm : certMode (⟨1047, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1047, by omega⟩ : Fin 1104) = 190817281666363690509286420348 := by decide +kernel
  have he : certE (⟨1047, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨1047, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1047, by omega⟩ : Fin 1104)).2.2 = 19375870806 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1048 :
    ((certNum ⟨1048, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1048, by omega⟩) ⟨1048, by omega⟩ (certE ⟨1048, by omega⟩) := by
  have hm : certMode (⟨1048, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1048, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1048, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1048, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1048, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1049 :
    ((certNum ⟨1049, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1049, by omega⟩) ⟨1049, by omega⟩ (certE ⟨1049, by omega⟩) := by
  have hm : certMode (⟨1049, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1049, by omega⟩ : Fin 1104) = 202772968629105435280114891037 := by decide +kernel
  have he : certE (⟨1049, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1049, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1049, by omega⟩ : Fin 1104)).2.2 = 20923056111 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1050 :
    ((certNum ⟨1050, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1050, by omega⟩) ⟨1050, by omega⟩ (certE ⟨1050, by omega⟩) := by
  have hm : certMode (⟨1050, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1050, by omega⟩ : Fin 1104) = 181584116270033516427915004466 := by decide +kernel
  have he : certE (⟨1050, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 9 else if j.val = 1 then -2 else if j.val = 2 then -5 else 0)) := by decide +kernel
  have hp : parent2 (⟨1050, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1050, by omega⟩ : Fin 1104)).2.2 = 18203053275 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1051 :
    ((certNum ⟨1051, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1051, by omega⟩) ⟨1051, by omega⟩ (certE ⟨1051, by omega⟩) := by
  have hm : certMode (⟨1051, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1051, by omega⟩ : Fin 1104) = 203308766348349456284404874430 := by decide +kernel
  have he : certE (⟨1051, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨1051, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1051, by omega⟩ : Fin 1104)).2.2 = 20993142869 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1052 :
    ((certNum ⟨1052, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1052, by omega⟩) ⟨1052, by omega⟩ (certE ⟨1052, by omega⟩) := by
  have hm : certMode (⟨1052, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1052, by omega⟩ : Fin 1104) = 89357656532725001520037650222 := by decide +kernel
  have he : certE (⟨1052, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then -30 else if j.val = 1 then -2 else if j.val = 2 then 4 else 6)) := by decide +kernel
  have hp : parent2 (⟨1052, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1052, by omega⟩ : Fin 1104)).2.2 = 7610664971 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1053 :
    ((certNum ⟨1053, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1053, by omega⟩) ⟨1053, by omega⟩ (certE ⟨1053, by omega⟩) := by
  have hm : certMode (⟨1053, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1053, by omega⟩ : Fin 1104) = 190863435458261261675910831802 := by decide +kernel
  have he : certE (⟨1053, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hp : parent2 (⟨1053, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1053, by omega⟩ : Fin 1104)).2.2 = 19381781896 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1054 :
    ((certNum ⟨1054, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1054, by omega⟩) ⟨1054, by omega⟩ (certE ⟨1054, by omega⟩) := by
  have hm : certMode (⟨1054, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1054, by omega⟩ : Fin 1104) = 203308759241918498503819793207 := by decide +kernel
  have he : certE (⟨1054, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨1054, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1054, by omega⟩ : Fin 1104)).2.2 = 20993141939 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1055 :
    ((certNum ⟨1055, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1055, by omega⟩) ⟨1055, by omega⟩ (certE ⟨1055, by omega⟩) := by
  have hm : certMode (⟨1055, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1055, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1055, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1055, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1055, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1056 :
    ((certNum ⟨1056, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1056, by omega⟩) ⟨1056, by omega⟩ (certE ⟨1056, by omega⟩) := by
  have hm : certMode (⟨1056, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1056, by omega⟩ : Fin 1104) = 18684028941379996809025615050 := by decide +kernel
  have he : certE (⟨1056, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -12 else if j.val = 1 then 5 else if j.val = 2 then 0 else -2)) := by decide +kernel
  have hp : parent2 (⟨1056, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1056, by omega⟩ : Fin 1104)).2.2 = 1210855911 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1057 :
    ((certNum ⟨1057, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1057, by omega⟩) ⟨1057, by omega⟩ (certE ⟨1057, by omega⟩) := by
  have hm : certMode (⟨1057, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1057, by omega⟩ : Fin 1104) = 202773010549570621802824967611 := by decide +kernel
  have he : certE (⟨1057, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1057, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1057, by omega⟩ : Fin 1104)).2.2 = 20923061592 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1058 :
    ((certNum ⟨1058, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1058, by omega⟩) ⟨1058, by omega⟩ (certE ⟨1058, by omega⟩) := by
  have hm : certMode (⟨1058, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1058, by omega⟩ : Fin 1104) = 10615919483582776759660422030 := by decide +kernel
  have he : certE (⟨1058, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 4 else if j.val = 1 then -8 else if j.val = 2 then 4 else -4)) := by decide +kernel
  have hp : parent2 (⟨1058, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1058, by omega⟩ : Fin 1104)).2.2 = 634805253 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1059 :
    ((certNum ⟨1059, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1059, by omega⟩) ⟨1059, by omega⟩ (certE ⟨1059, by omega⟩) := by
  have hm : certMode (⟨1059, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1059, by omega⟩ : Fin 1104) = 202773298325256846854664326432 := by decide +kernel
  have he : certE (⟨1059, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1059, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1059, by omega⟩ : Fin 1104)).2.2 = 20923099218 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1060 :
    ((certNum ⟨1060, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1060, by omega⟩) ⟨1060, by omega⟩ (certE ⟨1060, by omega⟩) := by
  have hm : certMode (⟨1060, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1060, by omega⟩ : Fin 1104) = 10616846263939397264968498726 := by decide +kernel
  have he : certE (⟨1060, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 0 else if j.val = 1 then -2 else if j.val = 2 then -2 else -1)) := by decide +kernel
  have hp : parent2 (⟨1060, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1060, by omega⟩ : Fin 1104)).2.2 = 634868206 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1061 :
    ((certNum ⟨1061, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1061, by omega⟩) ⟨1061, by omega⟩ (certE ⟨1061, by omega⟩) := by
  have hm : certMode (⟨1061, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1061, by omega⟩ : Fin 1104) = 202773126612859766607093553056 := by decide +kernel
  have he : certE (⟨1061, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1061, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1061, by omega⟩ : Fin 1104)).2.2 = 20923076767 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1062 :
    ((certNum ⟨1062, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1062, by omega⟩) ⟨1062, by omega⟩ (certE ⟨1062, by omega⟩) := by
  have hm : certMode (⟨1062, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1062, by omega⟩ : Fin 1104) = 203947278420543987643757705706 := by decide +kernel
  have he : certE (⟨1062, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1062, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1062, by omega⟩ : Fin 1104)).2.2 = 21076748618 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1063 :
    ((certNum ⟨1063, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1063, by omega⟩) ⟨1063, by omega⟩ (certE ⟨1063, by omega⟩) := by
  have hm : certMode (⟨1063, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1063, by omega⟩ : Fin 1104) = 5013305993788945121094341082 := by decide +kernel
  have he : certE (⟨1063, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -5 else if j.val = 1 then -2 else if j.val = 2 then -4 else 2)) := by decide +kernel
  have hp : parent2 (⟨1063, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1063, by omega⟩ : Fin 1104)).2.2 = 272205534 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1064 :
    ((certNum ⟨1064, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1064, by omega⟩) ⟨1064, by omega⟩ (certE ⟨1064, by omega⟩) := by
  have hm : certMode (⟨1064, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1064, by omega⟩ : Fin 1104) = 203947342177335403404123889790 := by decide +kernel
  have he : certE (⟨1064, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1064, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1064, by omega⟩ : Fin 1104)).2.2 = 21076756971 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1065 :
    ((certNum ⟨1065, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1065, by omega⟩) ⟨1065, by omega⟩ (certE ⟨1065, by omega⟩) := by
  have hm : certMode (⟨1065, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1065, by omega⟩ : Fin 1104) = 10481585426631097631064422524 := by decide +kernel
  have he : certE (⟨1065, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -21 else if j.val = 1 then 8 else if j.val = 2 then -1 else 0)) := by decide +kernel
  have hp : parent2 (⟨1065, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1065, by omega⟩ : Fin 1104)).2.2 = 625689464 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1066 :
    ((certNum ⟨1066, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1066, by omega⟩) ⟨1066, by omega⟩ (certE ⟨1066, by omega⟩) := by
  have hm : certMode (⟨1066, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1066, by omega⟩ : Fin 1104) = 203946854479128257908927509388 := by decide +kernel
  have he : certE (⟨1066, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1066, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1066, by omega⟩ : Fin 1104)).2.2 = 21076693076 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1067 :
    ((certNum ⟨1067, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1067, by omega⟩) ⟨1067, by omega⟩ (certE ⟨1067, by omega⟩) := by
  have hm : certMode (⟨1067, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1067, by omega⟩ : Fin 1104) = 5013158174026852321320052801 := by decide +kernel
  have he : certE (⟨1067, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -1 else if j.val = 1 then -8 else if j.val = 2 then 2 else -1)) := by decide +kernel
  have hp : parent2 (⟨1067, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1067, by omega⟩ : Fin 1104)).2.2 = 272196530 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1068 :
    ((certNum ⟨1068, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1068, by omega⟩) ⟨1068, by omega⟩ (certE ⟨1068, by omega⟩) := by
  have hm : certMode (⟨1068, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1068, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1068, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1068, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1068, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1069 :
    ((certNum ⟨1069, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1069, by omega⟩) ⟨1069, by omega⟩ (certE ⟨1069, by omega⟩) := by
  have hm : certMode (⟨1069, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1069, by omega⟩ : Fin 1104) = 203878523461884744522663064570 := by decide +kernel
  have he : certE (⟨1069, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1069, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1069, by omega⟩ : Fin 1104)).2.2 = 21067741424 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1070 :
    ((certNum ⟨1070, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1070, by omega⟩) ⟨1070, by omega⟩ (certE ⟨1070, by omega⟩) := by
  have hm : certMode (⟨1070, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1070, by omega⟩ : Fin 1104) = 154664965105562977071170594171 := by decide +kernel
  have he : certE (⟨1070, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -15 else if j.val = 1 then 1 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨1070, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1070, by omega⟩ : Fin 1104)).2.2 = 14895560886 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1071 :
    ((certNum ⟨1071, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1071, by omega⟩) ⟨1071, by omega⟩ (certE ⟨1071, by omega⟩) := by
  have hm : certMode (⟨1071, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1071, by omega⟩ : Fin 1104) = 204040279783518046888972505169 := by decide +kernel
  have he : certE (⟨1071, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨1071, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1071, by omega⟩ : Fin 1104)).2.2 = 21088933971 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1072 :
    ((certNum ⟨1072, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1072, by omega⟩) ⟨1072, by omega⟩ (certE ⟨1072, by omega⟩) := by
  have hm : certMode (⟨1072, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1072, by omega⟩ : Fin 1104) = 203879436088670253561955980473 := by decide +kernel
  have he : certE (⟨1072, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1072, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1072, by omega⟩ : Fin 1104)).2.2 = 21067860978 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1073 :
    ((certNum ⟨1073, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1073, by omega⟩) ⟨1073, by omega⟩ (certE ⟨1073, by omega⟩) := by
  have hm : certMode (⟨1073, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1073, by omega⟩ : Fin 1104) = 22967266812574251988724040174 := by decide +kernel
  have he : certE (⟨1073, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then 0 else -3)) := by decide +kernel
  have hp : parent2 (⟨1073, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1073, by omega⟩ : Fin 1104)).2.2 = 1535831075 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1074 :
    ((certNum ⟨1074, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1074, by omega⟩) ⟨1074, by omega⟩ (certE ⟨1074, by omega⟩) := by
  have hm : certMode (⟨1074, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1074, by omega⟩ : Fin 1104) = 203946721820801600807981558104 := by decide +kernel
  have he : certE (⟨1074, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1074, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1074, by omega⟩ : Fin 1104)).2.2 = 21076675696 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1075 :
    ((certNum ⟨1075, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1075, by omega⟩) ⟨1075, by omega⟩ (certE ⟨1075, by omega⟩) := by
  have hm : certMode (⟨1075, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1075, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1075, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1075, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1075, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1076 :
    ((certNum ⟨1076, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1076, by omega⟩) ⟨1076, by omega⟩ (certE ⟨1076, by omega⟩) := by
  have hm : certMode (⟨1076, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1076, by omega⟩ : Fin 1104) = 154646569738126147338588103819 := by decide +kernel
  have he : certE (⟨1076, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -14 else if j.val = 1 then -3 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hp : parent2 (⟨1076, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1076, by omega⟩ : Fin 1104)).2.2 = 14893358613 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1077 :
    ((certNum ⟨1077, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1077, by omega⟩) ⟨1077, by omega⟩ (certE ⟨1077, by omega⟩) := by
  have hm : certMode (⟨1077, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1077, by omega⟩ : Fin 1104) = 203947332277592689048412270275 := by decide +kernel
  have he : certE (⟨1077, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1077, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1077, by omega⟩ : Fin 1104)).2.2 = 21076755674 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1078 :
    ((certNum ⟨1078, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1078, by omega⟩) ⟨1078, by omega⟩ (certE ⟨1078, by omega⟩) := by
  have hm : certMode (⟨1078, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1078, by omega⟩ : Fin 1104) = 203971880994425769932804342800 := by decide +kernel
  have he : certE (⟨1078, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 1 else if j.val = 1 then -2 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hp : parent2 (⟨1078, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1078, by omega⟩ : Fin 1104)).2.2 = 21079971939 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1079 :
    ((certNum ⟨1079, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1079, by omega⟩) ⟨1079, by omega⟩ (certE ⟨1079, by omega⟩) := by
  have hm : certMode (⟨1079, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1079, by omega⟩ : Fin 1104) = 22966164379560423406240122310 := by decide +kernel
  have he : certE (⟨1079, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then 0 else -3)) := by decide +kernel
  have hp : parent2 (⟨1079, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1079, by omega⟩ : Fin 1104)).2.2 = 1535745953 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1080 :
    ((certNum ⟨1080, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1080, by omega⟩) ⟨1080, by omega⟩ (certE ⟨1080, by omega⟩) := by
  have hm : certMode (⟨1080, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1080, by omega⟩ : Fin 1104) = 203308687772609204217085680883 := by decide +kernel
  have he : certE (⟨1080, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨1080, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1080, by omega⟩ : Fin 1104)).2.2 = 20993132586 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1081 :
    ((certNum ⟨1081, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1081, by omega⟩) ⟨1081, by omega⟩ (certE ⟨1081, by omega⟩) := by
  have hm : certMode (⟨1081, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1081, by omega⟩ : Fin 1104) = 10583313136248242720070015874 := by decide +kernel
  have he : certE (⟨1081, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -5 else if j.val = 1 then -6 else if j.val = 2 then -8 else 8)) := by decide +kernel
  have hp : parent2 (⟨1081, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1081, by omega⟩ : Fin 1104)).2.2 = 632590968 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1082 :
    ((certNum ⟨1082, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1082, by omega⟩) ⟨1082, by omega⟩ (certE ⟨1082, by omega⟩) := by
  have hm : certMode (⟨1082, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1082, by omega⟩ : Fin 1104) = 203309014737106646720085508080 := by decide +kernel
  have he : certE (⟨1082, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨1082, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1082, by omega⟩ : Fin 1104)).2.2 = 20993175375 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1083 :
    ((certNum ⟨1083, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1083, by omega⟩) ⟨1083, by omega⟩ (certE ⟨1083, by omega⟩) := by
  have hm : certMode (⟨1083, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1083, by omega⟩ : Fin 1104) = 5069675318829323065349414476 := by decide +kernel
  have he : certE (⟨1083, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then 2 else if j.val = 2 then -5 else 2)) := by decide +kernel
  have hp : parent2 (⟨1083, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1083, by omega⟩ : Fin 1104)).2.2 = 275641776 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1084 :
    ((certNum ⟨1084, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1084, by omega⟩) ⟨1084, by omega⟩ (certE ⟨1084, by omega⟩) := by
  have hm : certMode (⟨1084, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1084, by omega⟩ : Fin 1104) = 203308690806215437205980593519 := by decide +kernel
  have he : certE (⟨1084, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨1084, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1084, by omega⟩ : Fin 1104)).2.2 = 20993132983 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1085 :
    ((certNum ⟨1085, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1085, by omega⟩) ⟨1085, by omega⟩ (certE ⟨1085, by omega⟩) := by
  have hm : certMode (⟨1085, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1085, by omega⟩ : Fin 1104) = 5070884424179939696612421429 := by decide +kernel
  have he : certE (⟨1085, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -14 else if j.val = 1 then 1 else if j.val = 2 then -7 else 6)) := by decide +kernel
  have hp : parent2 (⟨1085, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1085, by omega⟩ : Fin 1104)).2.2 = 275715540 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1086 :
    ((certNum ⟨1086, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1086, by omega⟩) ⟨1086, by omega⟩ (certE ⟨1086, by omega⟩) := by
  have hm : certMode (⟨1086, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1086, by omega⟩ : Fin 1104) = 203946121460980584059406151191 := by decide +kernel
  have he : certE (⟨1086, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1086, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1086, by omega⟩ : Fin 1104)).2.2 = 21076597041 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1087 :
    ((certNum ⟨1087, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1087, by omega⟩) ⟨1087, by omega⟩ (certE ⟨1087, by omega⟩) := by
  have hm : certMode (⟨1087, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1087, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1087, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1087, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1087, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1088 :
    ((certNum ⟨1088, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1088, by omega⟩) ⟨1088, by omega⟩ (certE ⟨1088, by omega⟩) := by
  have hm : certMode (⟨1088, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1088, by omega⟩ : Fin 1104) = 203944899411439485644257561055 := by decide +kernel
  have he : certE (⟨1088, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1088, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1088, by omega⟩ : Fin 1104)).2.2 = 21076436937 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1089 :
    ((certNum ⟨1089, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1089, by omega⟩) ⟨1089, by omega⟩ (certE ⟨1089, by omega⟩) := by
  have hm : certMode (⟨1089, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1089, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1089, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1089, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1089, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1090 :
    ((certNum ⟨1090, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1090, by omega⟩) ⟨1090, by omega⟩ (certE ⟨1090, by omega⟩) := by
  have hm : certMode (⟨1090, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1090, by omega⟩ : Fin 1104) = 203945881637288174198467490782 := by decide +kernel
  have he : certE (⟨1090, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1090, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1090, by omega⟩ : Fin 1104)).2.2 = 21076565621 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1091 :
    ((certNum ⟨1091, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1091, by omega⟩) ⟨1091, by omega⟩ (certE ⟨1091, by omega⟩) := by
  have hm : certMode (⟨1091, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1091, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1091, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1091, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1091, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1092 :
    ((certNum ⟨1092, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1092, by omega⟩) ⟨1092, by omega⟩ (certE ⟨1092, by omega⟩) := by
  have hm : certMode (⟨1092, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1092, by omega⟩ : Fin 1104) = 203873601637565955476515406044 := by decide +kernel
  have he : certE (⟨1092, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1092, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1092, by omega⟩ : Fin 1104)).2.2 = 21067096672 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1093 :
    ((certNum ⟨1093, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1093, by omega⟩) ⟨1093, by omega⟩ (certE ⟨1093, by omega⟩) := by
  have hm : certMode (⟨1093, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1093, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1093, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1093, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1093, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1094 :
    ((certNum ⟨1094, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1094, by omega⟩) ⟨1094, by omega⟩ (certE ⟨1094, by omega⟩) := by
  have hm : certMode (⟨1094, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1094, by omega⟩ : Fin 1104) = 203876051895788238653041340463 := by decide +kernel
  have he : certE (⟨1094, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1094, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1094, by omega⟩ : Fin 1104)).2.2 = 21067417651 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1095 :
    ((certNum ⟨1095, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1095, by omega⟩) ⟨1095, by omega⟩ (certE ⟨1095, by omega⟩) := by
  have hm : certMode (⟨1095, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1095, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1095, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1095, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1095, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1096 :
    ((certNum ⟨1096, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1096, by omega⟩) ⟨1096, by omega⟩ (certE ⟨1096, by omega⟩) := by
  have hm : certMode (⟨1096, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1096, by omega⟩ : Fin 1104) = 203876652871172760195802593591 := by decide +kernel
  have he : certE (⟨1096, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨1096, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1096, by omega⟩ : Fin 1104)).2.2 = 21067496378 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1097 :
    ((certNum ⟨1097, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1097, by omega⟩) ⟨1097, by omega⟩ (certE ⟨1097, by omega⟩) := by
  have hm : certMode (⟨1097, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1097, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1097, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1097, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1097, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1098 :
    ((certNum ⟨1098, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1098, by omega⟩) ⟨1098, by omega⟩ (certE ⟨1098, by omega⟩) := by
  have hm : certMode (⟨1098, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1098, by omega⟩ : Fin 1104) = 86497117428266109130801901 := by decide +kernel
  have he : certE (⟨1098, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -18 else if j.val = 1 then 3 else if j.val = 2 then -7 else 4)) := by decide +kernel
  have hp : parent2 (⟨1098, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1098, by omega⟩ : Fin 1104)).2.2 = 3165320 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1099 :
    ((certNum ⟨1099, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1099, by omega⟩) ⟨1099, by omega⟩ (certE ⟨1099, by omega⟩) := by
  have hm : certMode (⟨1099, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1099, by omega⟩ : Fin 1104) = 86497471999505336911291180 := by decide +kernel
  have he : certE (⟨1099, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -18 else if j.val = 1 then 3 else if j.val = 2 then -7 else 4)) := by decide +kernel
  have hp : parent2 (⟨1099, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1099, by omega⟩ : Fin 1104)).2.2 = 3165334 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1100 :
    ((certNum ⟨1100, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1100, by omega⟩) ⟨1100, by omega⟩ (certE ⟨1100, by omega⟩) := by
  have hm : certMode (⟨1100, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1100, by omega⟩ : Fin 1104) = 121937677940167328024166040 := by decide +kernel
  have he : certE (⟨1100, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -39 else if j.val = 1 then -6 else if j.val = 2 then 6 else 6)) := by decide +kernel
  have hp : parent2 (⟨1100, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1100, by omega⟩ : Fin 1104)).2.2 = 4586770 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1101 :
    ((certNum ⟨1101, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1101, by omega⟩) ⟨1101, by omega⟩ (certE ⟨1101, by omega⟩) := by
  have hm : certMode (⟨1101, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1101, by omega⟩ : Fin 1104) = 121755444654439951737018916 := by decide +kernel
  have he : certE (⟨1101, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -22 else if j.val = 1 then 0 else if j.val = 2 then -3 else 4)) := by decide +kernel
  have hp : parent2 (⟨1101, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1101, by omega⟩ : Fin 1104)).2.2 = 4579358 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1102 :
    ((certNum ⟨1102, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1102, by omega⟩) ⟨1102, by omega⟩ (certE ⟨1102, by omega⟩) := by
  have hm : certMode (⟨1102, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1102, by omega⟩ : Fin 1104) = 121936866646228059733658613 := by decide +kernel
  have he : certE (⟨1102, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -39 else if j.val = 1 then -6 else if j.val = 2 then 6 else 6)) := by decide +kernel
  have hp : parent2 (⟨1102, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1102, by omega⟩ : Fin 1104)).2.2 = 4586737 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1103 :
    ((certNum ⟨1103, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1103, by omega⟩) ⟨1103, by omega⟩ (certE ⟨1103, by omega⟩) := by
  have hm : certMode (⟨1103, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1103, by omega⟩ : Fin 1104) = 121776245834896327342422888 := by decide +kernel
  have he : certE (⟨1103, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -23 else if j.val = 1 then 4 else if j.val = 2 then 8 else -7)) := by decide +kernel
  have hp : parent2 (⟨1103, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1103, by omega⟩ : Fin 1104)).2.2 = 4580204 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨1012 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1012 + j.val, by omega⟩) ⟨1012 + j.val, by omega⟩
        (certE ⟨1012 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_1012
  | ⟨1, _⟩ => exact MME.L2Cert.cert_1013
  | ⟨2, _⟩ => exact MME.L2Cert.cert_1014
  | ⟨3, _⟩ => exact MME.L2Cert.cert_1015
  | ⟨4, _⟩ => exact MME.L2Cert.cert_1016
  | ⟨5, _⟩ => exact MME.L2Cert.cert_1017
  | ⟨6, _⟩ => exact MME.L2Cert.cert_1018
  | ⟨7, _⟩ => exact MME.L2Cert.cert_1019
  | ⟨8, _⟩ => exact MME.L2Cert.cert_1020
  | ⟨9, _⟩ => exact MME.L2Cert.cert_1021
  | ⟨10, _⟩ => exact MME.L2Cert.cert_1022
  | ⟨11, _⟩ => exact MME.L2Cert.cert_1023
  | ⟨12, _⟩ => exact MME.L2Cert.cert_1024
  | ⟨13, _⟩ => exact MME.L2Cert.cert_1025
  | ⟨14, _⟩ => exact MME.L2Cert.cert_1026
  | ⟨15, _⟩ => exact MME.L2Cert.cert_1027
  | ⟨16, _⟩ => exact MME.L2Cert.cert_1028
  | ⟨17, _⟩ => exact MME.L2Cert.cert_1029
  | ⟨18, _⟩ => exact MME.L2Cert.cert_1030
  | ⟨19, _⟩ => exact MME.L2Cert.cert_1031
  | ⟨20, _⟩ => exact MME.L2Cert.cert_1032
  | ⟨21, _⟩ => exact MME.L2Cert.cert_1033
  | ⟨22, _⟩ => exact MME.L2Cert.cert_1034
  | ⟨23, _⟩ => exact MME.L2Cert.cert_1035
  | ⟨24, _⟩ => exact MME.L2Cert.cert_1036
  | ⟨25, _⟩ => exact MME.L2Cert.cert_1037
  | ⟨26, _⟩ => exact MME.L2Cert.cert_1038
  | ⟨27, _⟩ => exact MME.L2Cert.cert_1039
  | ⟨28, _⟩ => exact MME.L2Cert.cert_1040
  | ⟨29, _⟩ => exact MME.L2Cert.cert_1041
  | ⟨30, _⟩ => exact MME.L2Cert.cert_1042
  | ⟨31, _⟩ => exact MME.L2Cert.cert_1043
  | ⟨32, _⟩ => exact MME.L2Cert.cert_1044
  | ⟨33, _⟩ => exact MME.L2Cert.cert_1045
  | ⟨34, _⟩ => exact MME.L2Cert.cert_1046
  | ⟨35, _⟩ => exact MME.L2Cert.cert_1047
  | ⟨36, _⟩ => exact MME.L2Cert.cert_1048
  | ⟨37, _⟩ => exact MME.L2Cert.cert_1049
  | ⟨38, _⟩ => exact MME.L2Cert.cert_1050
  | ⟨39, _⟩ => exact MME.L2Cert.cert_1051
  | ⟨40, _⟩ => exact MME.L2Cert.cert_1052
  | ⟨41, _⟩ => exact MME.L2Cert.cert_1053
  | ⟨42, _⟩ => exact MME.L2Cert.cert_1054
  | ⟨43, _⟩ => exact MME.L2Cert.cert_1055
  | ⟨44, _⟩ => exact MME.L2Cert.cert_1056
  | ⟨45, _⟩ => exact MME.L2Cert.cert_1057
  | ⟨46, _⟩ => exact MME.L2Cert.cert_1058
  | ⟨47, _⟩ => exact MME.L2Cert.cert_1059
  | ⟨48, _⟩ => exact MME.L2Cert.cert_1060
  | ⟨49, _⟩ => exact MME.L2Cert.cert_1061
  | ⟨50, _⟩ => exact MME.L2Cert.cert_1062
  | ⟨51, _⟩ => exact MME.L2Cert.cert_1063
  | ⟨52, _⟩ => exact MME.L2Cert.cert_1064
  | ⟨53, _⟩ => exact MME.L2Cert.cert_1065
  | ⟨54, _⟩ => exact MME.L2Cert.cert_1066
  | ⟨55, _⟩ => exact MME.L2Cert.cert_1067
  | ⟨56, _⟩ => exact MME.L2Cert.cert_1068
  | ⟨57, _⟩ => exact MME.L2Cert.cert_1069
  | ⟨58, _⟩ => exact MME.L2Cert.cert_1070
  | ⟨59, _⟩ => exact MME.L2Cert.cert_1071
  | ⟨60, _⟩ => exact MME.L2Cert.cert_1072
  | ⟨61, _⟩ => exact MME.L2Cert.cert_1073
  | ⟨62, _⟩ => exact MME.L2Cert.cert_1074
  | ⟨63, _⟩ => exact MME.L2Cert.cert_1075
  | ⟨64, _⟩ => exact MME.L2Cert.cert_1076
  | ⟨65, _⟩ => exact MME.L2Cert.cert_1077
  | ⟨66, _⟩ => exact MME.L2Cert.cert_1078
  | ⟨67, _⟩ => exact MME.L2Cert.cert_1079
  | ⟨68, _⟩ => exact MME.L2Cert.cert_1080
  | ⟨69, _⟩ => exact MME.L2Cert.cert_1081
  | ⟨70, _⟩ => exact MME.L2Cert.cert_1082
  | ⟨71, _⟩ => exact MME.L2Cert.cert_1083
  | ⟨72, _⟩ => exact MME.L2Cert.cert_1084
  | ⟨73, _⟩ => exact MME.L2Cert.cert_1085
  | ⟨74, _⟩ => exact MME.L2Cert.cert_1086
  | ⟨75, _⟩ => exact MME.L2Cert.cert_1087
  | ⟨76, _⟩ => exact MME.L2Cert.cert_1088
  | ⟨77, _⟩ => exact MME.L2Cert.cert_1089
  | ⟨78, _⟩ => exact MME.L2Cert.cert_1090
  | ⟨79, _⟩ => exact MME.L2Cert.cert_1091
  | ⟨80, _⟩ => exact MME.L2Cert.cert_1092
  | ⟨81, _⟩ => exact MME.L2Cert.cert_1093
  | ⟨82, _⟩ => exact MME.L2Cert.cert_1094
  | ⟨83, _⟩ => exact MME.L2Cert.cert_1095
  | ⟨84, _⟩ => exact MME.L2Cert.cert_1096
  | ⟨85, _⟩ => exact MME.L2Cert.cert_1097
  | ⟨86, _⟩ => exact MME.L2Cert.cert_1098
  | ⟨87, _⟩ => exact MME.L2Cert.cert_1099
  | ⟨88, _⟩ => exact MME.L2Cert.cert_1100
  | ⟨89, _⟩ => exact MME.L2Cert.cert_1101
  | ⟨90, _⟩ => exact MME.L2Cert.cert_1102
  | ⟨91, _⟩ => exact MME.L2Cert.cert_1103
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
