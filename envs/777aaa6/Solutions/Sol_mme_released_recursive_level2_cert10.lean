-- Prove2me | solution 1 for mme_released_recursive_level2_cert10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T01:01:47.29021+00:00
-- url     : https://prove2.me/submissions/6f1d59df-627d-40c4-99b7-04eba81ab816

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

theorem cert_920 :
    ((certNum ⟨920, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨920, by omega⟩) ⟨920, by omega⟩ (certE ⟨920, by omega⟩) := by
  have hm : certMode (⟨920, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨920, by omega⟩ : Fin 1104) = 203944565267356086030183851541 := by decide +kernel
  have he : certE (⟨920, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨920, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨920, by omega⟩ : Fin 1104)).2.2 = 21076393160 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_921 :
    ((certNum ⟨921, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨921, by omega⟩) ⟨921, by omega⟩ (certE ⟨921, by omega⟩) := by
  have hm : certMode (⟨921, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨921, by omega⟩ : Fin 1104) = 203944554253120406487754543767 := by decide +kernel
  have he : certE (⟨921, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨921, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨921, by omega⟩ : Fin 1104)).2.2 = 21076391717 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_922 :
    ((certNum ⟨922, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨922, by omega⟩) ⟨922, by omega⟩ (certE ⟨922, by omega⟩) := by
  have hm : certMode (⟨922, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨922, by omega⟩ : Fin 1104) = 203944565282621831661464703032 := by decide +kernel
  have he : certE (⟨922, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨922, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨922, by omega⟩ : Fin 1104)).2.2 = 21076393162 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_923 :
    ((certNum ⟨923, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨923, by omega⟩) ⟨923, by omega⟩ (certE ⟨923, by omega⟩) := by
  have hm : certMode (⟨923, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨923, by omega⟩ : Fin 1104) = 203944554237854660283851946033 := by decide +kernel
  have he : certE (⟨923, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨923, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨923, by omega⟩ : Fin 1104)).2.2 = 21076391715 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_924 :
    ((certNum ⟨924, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨924, by omega⟩) ⟨924, by omega⟩ (certE ⟨924, by omega⟩) := by
  have hm : certMode (⟨924, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨924, by omega⟩ : Fin 1104) = 203944552650217050750625747870 := by decide +kernel
  have he : certE (⟨924, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨924, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨924, by omega⟩ : Fin 1104)).2.2 = 21076391507 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_925 :
    ((certNum ⟨925, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨925, by omega⟩) ⟨925, by omega⟩ (certE ⟨925, by omega⟩) := by
  have hm : certMode (⟨925, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨925, by omega⟩ : Fin 1104) = 203944552657849923893889030852 := by decide +kernel
  have he : certE (⟨925, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨925, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨925, by omega⟩ : Fin 1104)).2.2 = 21076391508 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_926 :
    ((certNum ⟨926, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨926, by omega⟩) ⟨926, by omega⟩ (certE ⟨926, by omega⟩) := by
  have hm : certMode (⟨926, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨926, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨926, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨926, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨926, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_927 :
    ((certNum ⟨927, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨927, by omega⟩) ⟨927, by omega⟩ (certE ⟨927, by omega⟩) := by
  have hm : certMode (⟨927, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨927, by omega⟩ : Fin 1104) = 203876128156149355295937554098 := by decide +kernel
  have he : certE (⟨927, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨927, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨927, by omega⟩ : Fin 1104)).2.2 = 21067427641 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_928 :
    ((certNum ⟨928, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨928, by omega⟩) ⟨928, by omega⟩ (certE ⟨928, by omega⟩) := by
  have hm : certMode (⟨928, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨928, by omega⟩ : Fin 1104) = 203947243401244556474262345006 := by decide +kernel
  have he : certE (⟨928, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨928, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨928, by omega⟩ : Fin 1104)).2.2 = 21076744030 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_929 :
    ((certNum ⟨929, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨929, by omega⟩) ⟨929, by omega⟩ (certE ⟨929, by omega⟩) := by
  have hm : certMode (⟨929, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨929, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨929, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨929, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨929, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_930 :
    ((certNum ⟨930, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨930, by omega⟩) ⟨930, by omega⟩ (certE ⟨930, by omega⟩) := by
  have hm : certMode (⟨930, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨930, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨930, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨930, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨930, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_931 :
    ((certNum ⟨931, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨931, by omega⟩) ⟨931, by omega⟩ (certE ⟨931, by omega⟩) := by
  have hm : certMode (⟨931, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨931, by omega⟩ : Fin 1104) = 203875361658466718532255210390 := by decide +kernel
  have he : certE (⟨931, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨931, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨931, by omega⟩ : Fin 1104)).2.2 = 21067327231 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_932 :
    ((certNum ⟨932, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨932, by omega⟩) ⟨932, by omega⟩ (certE ⟨932, by omega⟩) := by
  have hm : certMode (⟨932, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨932, by omega⟩ : Fin 1104) = 39760938098677264529155795859 := by decide +kernel
  have he : certE (⟨932, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -16 else if j.val = 1 then -2 else if j.val = 2 then 1 else 3)) := by decide +kernel
  have hp : parent2 (⟨932, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨932, by omega⟩ : Fin 1104)).2.2 = 2907550874 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_933 :
    ((certNum ⟨933, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨933, by omega⟩) ⟨933, by omega⟩ (certE ⟨933, by omega⟩) := by
  have hm : certMode (⟨933, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨933, by omega⟩ : Fin 1104) = 203872139796694871949716398236 := by decide +kernel
  have he : certE (⟨933, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨933, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨933, by omega⟩ : Fin 1104)).2.2 = 21066905175 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_934 :
    ((certNum ⟨934, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨934, by omega⟩) ⟨934, by omega⟩ (certE ⟨934, by omega⟩) := by
  have hm : certMode (⟨934, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨934, by omega⟩ : Fin 1104) = 203947223700978592629554463818 := by decide +kernel
  have he : certE (⟨934, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨934, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨934, by omega⟩ : Fin 1104)).2.2 = 21076741449 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_935 :
    ((certNum ⟨935, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨935, by omega⟩) ⟨935, by omega⟩ (certE ⟨935, by omega⟩) := by
  have hm : certMode (⟨935, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨935, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨935, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨935, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨935, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_936 :
    ((certNum ⟨936, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨936, by omega⟩) ⟨936, by omega⟩ (certE ⟨936, by omega⟩) := by
  have hm : certMode (⟨936, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨936, by omega⟩ : Fin 1104) = 15741724245369973577230324100 := by decide +kernel
  have he : certE (⟨936, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 12 else if j.val = 1 then 0 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨936, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨936, by omega⟩ : Fin 1104)).2.2 = 994804490 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_937 :
    ((certNum ⟨937, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨937, by omega⟩) ⟨937, by omega⟩ (certE ⟨937, by omega⟩) := by
  have hm : certMode (⟨937, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨937, by omega⟩ : Fin 1104) = 203308678136897510646208915773 := by decide +kernel
  have he : certE (⟨937, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨937, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨937, by omega⟩ : Fin 1104)).2.2 = 20993131325 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_938 :
    ((certNum ⟨938, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨938, by omega⟩) ⟨938, by omega⟩ (certE ⟨938, by omega⟩) := by
  have hm : certMode (⟨938, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨938, by omega⟩ : Fin 1104) = 15741992803872173317035541358 := by decide +kernel
  have he : certE (⟨938, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 8 else if j.val = 1 then 6 else if j.val = 2 then -7 else -4)) := by decide +kernel
  have hp : parent2 (⟨938, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨938, by omega⟩ : Fin 1104)).2.2 = 994823920 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_939 :
    ((certNum ⟨939, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨939, by omega⟩) ⟨939, by omega⟩ (certE ⟨939, by omega⟩) := by
  have hm : certMode (⟨939, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨939, by omega⟩ : Fin 1104) = 203308694871400566768902851231 := by decide +kernel
  have he : certE (⟨939, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨939, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨939, by omega⟩ : Fin 1104)).2.2 = 20993133515 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_940 :
    ((certNum ⟨940, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨940, by omega⟩) ⟨940, by omega⟩ (certE ⟨940, by omega⟩) := by
  have hm : certMode (⟨940, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨940, by omega⟩ : Fin 1104) = 25358840252824773255855384690 := by decide +kernel
  have he : certE (⟨940, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -7 else if j.val = 1 then -4 else if j.val = 2 then 3 else -1)) := by decide +kernel
  have hp : parent2 (⟨940, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨940, by omega⟩ : Fin 1104)).2.2 = 1722175896 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_941 :
    ((certNum ⟨941, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨941, by omega⟩) ⟨941, by omega⟩ (certE ⟨941, by omega⟩) := by
  have hm : certMode (⟨941, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨941, by omega⟩ : Fin 1104) = 203308684777209568087942578167 := by decide +kernel
  have he : certE (⟨941, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨941, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨941, by omega⟩ : Fin 1104)).2.2 = 20993132194 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_942 :
    ((certNum ⟨942, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨942, by omega⟩) ⟨942, by omega⟩ (certE ⟨942, by omega⟩) := by
  have hm : certMode (⟨942, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨942, by omega⟩ : Fin 1104) = 203947306135248144122624042177 := by decide +kernel
  have he : certE (⟨942, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨942, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨942, by omega⟩ : Fin 1104)).2.2 = 21076752249 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_943 :
    ((certNum ⟨943, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨943, by omega⟩) ⟨943, by omega⟩ (certE ⟨943, by omega⟩) := by
  have hm : certMode (⟨943, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨943, by omega⟩ : Fin 1104) = 10399229628021736524319312821 := by decide +kernel
  have he : certE (⟨943, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -11 else if j.val = 1 then 4 else if j.val = 2 then -5 else 2)) := by decide +kernel
  have hp : parent2 (⟨943, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨943, by omega⟩ : Fin 1104)).2.2 = 620109772 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_944 :
    ((certNum ⟨944, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨944, by omega⟩) ⟨944, by omega⟩ (certE ⟨944, by omega⟩) := by
  have hm : certMode (⟨944, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨944, by omega⟩ : Fin 1104) = 203947232852710213840964370217 := by decide +kernel
  have he : certE (⟨944, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨944, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨944, by omega⟩ : Fin 1104)).2.2 = 21076742648 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_945 :
    ((certNum ⟨945, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨945, by omega⟩) ⟨945, by omega⟩ (certE ⟨945, by omega⟩) := by
  have hm : certMode (⟨945, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨945, by omega⟩ : Fin 1104) = 10399940632678836204401906424 := by decide +kernel
  have he : certE (⟨945, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -11 else if j.val = 1 then 4 else if j.val = 2 then -5 else 2)) := by decide +kernel
  have hp : parent2 (⟨945, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨945, by omega⟩ : Fin 1104)).2.2 = 620157914 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_946 :
    ((certNum ⟨946, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨946, by omega⟩) ⟨946, by omega⟩ (certE ⟨946, by omega⟩) := by
  have hm : certMode (⟨946, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨946, by omega⟩ : Fin 1104) = 203947340933188881670083620246 := by decide +kernel
  have he : certE (⟨946, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨946, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨946, by omega⟩ : Fin 1104)).2.2 = 21076756808 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_947 :
    ((certNum ⟨947, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨947, by omega⟩) ⟨947, by omega⟩ (certE ⟨947, by omega⟩) := by
  have hm : certMode (⟨947, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨947, by omega⟩ : Fin 1104) = 18363453403021012811562611927 := by decide +kernel
  have he : certE (⟨947, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -18 else if j.val = 1 then 4 else if j.val = 2 then -4 else 4)) := by decide +kernel
  have hp : parent2 (⟨947, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨947, by omega⟩ : Fin 1104)).2.2 = 1187017471 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_948 :
    ((certNum ⟨948, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨948, by omega⟩) ⟨948, by omega⟩ (certE ⟨948, by omega⟩) := by
  have hm : certMode (⟨948, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨948, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨948, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨948, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨948, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_949 :
    ((certNum ⟨949, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨949, by omega⟩) ⟨949, by omega⟩ (certE ⟨949, by omega⟩) := by
  have hm : certMode (⟨949, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨949, by omega⟩ : Fin 1104) = 180599777681286175518065762601 := by decide +kernel
  have he : certE (⟨949, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨949, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨949, by omega⟩ : Fin 1104)).2.2 = 18079163031 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_950 :
    ((certNum ⟨950, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨950, by omega⟩) ⟨950, by omega⟩ (certE ⟨950, by omega⟩) := by
  have hm : certMode (⟨950, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨950, by omega⟩ : Fin 1104) = 203946007525668990567812150591 := by decide +kernel
  have he : certE (⟨950, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨950, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨950, by omega⟩ : Fin 1104)).2.2 = 21076582114 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_951 :
    ((certNum ⟨951, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨951, by omega⟩) ⟨951, by omega⟩ (certE ⟨951, by omega⟩) := by
  have hm : certMode (⟨951, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨951, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨951, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨951, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨951, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_952 :
    ((certNum ⟨952, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨952, by omega⟩) ⟨952, by omega⟩ (certE ⟨952, by omega⟩) := by
  have hm : certMode (⟨952, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨952, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨952, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨952, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨952, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_953 :
    ((certNum ⟨953, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨953, by omega⟩) ⟨953, by omega⟩ (certE ⟨953, by omega⟩) := by
  have hm : certMode (⟨953, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨953, by omega⟩ : Fin 1104) = 180605578561892214882056954894 := by decide +kernel
  have he : certE (⟨953, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨953, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨953, by omega⟩ : Fin 1104)).2.2 = 18079892491 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_954 :
    ((certNum ⟨954, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨954, by omega⟩) ⟨954, by omega⟩ (certE ⟨954, by omega⟩) := by
  have hm : certMode (⟨954, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨954, by omega⟩ : Fin 1104) = 203945738796311083902160146124 := by decide +kernel
  have he : certE (⟨954, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨954, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨954, by omega⟩ : Fin 1104)).2.2 = 21076546907 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_955 :
    ((certNum ⟨955, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨955, by omega⟩) ⟨955, by omega⟩ (certE ⟨955, by omega⟩) := by
  have hm : certMode (⟨955, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨955, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨955, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨955, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨955, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_956 :
    ((certNum ⟨956, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨956, by omega⟩) ⟨956, by omega⟩ (certE ⟨956, by omega⟩) := by
  have hm : certMode (⟨956, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨956, by omega⟩ : Fin 1104) = 203944711719250331980689170240 := by decide +kernel
  have he : certE (⟨956, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨956, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨956, by omega⟩ : Fin 1104)).2.2 = 21076412347 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_957 :
    ((certNum ⟨957, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨957, by omega⟩) ⟨957, by omega⟩ (certE ⟨957, by omega⟩) := by
  have hm : certMode (⟨957, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨957, by omega⟩ : Fin 1104) = 152258563623632744367366676 := by decide +kernel
  have he : certE (⟨957, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -3 else if j.val = 1 then -7 else if j.val = 2 then 1 else -2)) := by decide +kernel
  have hp : parent2 (⟨957, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨957, by omega⟩ : Fin 1104)).2.2 = 5832764 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_958 :
    ((certNum ⟨958, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨958, by omega⟩) ⟨958, by omega⟩ (certE ⟨958, by omega⟩) := by
  have hm : certMode (⟨958, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨958, by omega⟩ : Fin 1104) = 179718151366886553196340254842 := by decide +kernel
  have he : certE (⟨958, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 19 else if j.val = 1 then 2 else if j.val = 2 then -6 else -5)) := by decide +kernel
  have hp : parent2 (⟨958, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨958, by omega⟩ : Fin 1104)).2.2 = 17968387899 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_959 :
    ((certNum ⟨959, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨959, by omega⟩) ⟨959, by omega⟩ (certE ⟨959, by omega⟩) := by
  have hm : certMode (⟨959, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨959, by omega⟩ : Fin 1104) = 179719241092055783027958317247 := by decide +kernel
  have he : certE (⟨959, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨959, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨959, by omega⟩ : Fin 1104)).2.2 = 17968524713 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_960 :
    ((certNum ⟨960, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨960, by omega⟩) ⟨960, by omega⟩ (certE ⟨960, by omega⟩) := by
  have hm : certMode (⟨960, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨960, by omega⟩ : Fin 1104) = 179717994934862663063516098556 := by decide +kernel
  have he : certE (⟨960, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 19 else if j.val = 1 then 2 else if j.val = 2 then -6 else -5)) := by decide +kernel
  have hp : parent2 (⟨960, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨960, by omega⟩ : Fin 1104)).2.2 = 17968368259 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_961 :
    ((certNum ⟨961, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨961, by omega⟩) ⟨961, by omega⟩ (certE ⟨961, by omega⟩) := by
  have hm : certMode (⟨961, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨961, by omega⟩ : Fin 1104) = 179717939689804837820234526118 := by decide +kernel
  have he : certE (⟨961, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 19 else if j.val = 1 then 2 else if j.val = 2 then -6 else -5)) := by decide +kernel
  have hp : parent2 (⟨961, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨961, by omega⟩ : Fin 1104)).2.2 = 17968361323 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_962 :
    ((certNum ⟨962, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨962, by omega⟩) ⟨962, by omega⟩ (certE ⟨962, by omega⟩) := by
  have hm : certMode (⟨962, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨962, by omega⟩ : Fin 1104) = 179719239801725142987768731466 := by decide +kernel
  have he : certE (⟨962, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨962, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨962, by omega⟩ : Fin 1104)).2.2 = 17968524551 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_963 :
    ((certNum ⟨963, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨963, by omega⟩) ⟨963, by omega⟩ (certE ⟨963, by omega⟩) := by
  have hm : certMode (⟨963, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨963, by omega⟩ : Fin 1104) = 179718455677825423417224355054 := by decide +kernel
  have he : certE (⟨963, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨963, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨963, by omega⟩ : Fin 1104)).2.2 = 17968426105 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_964 :
    ((certNum ⟨964, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨964, by omega⟩) ⟨964, by omega⟩ (certE ⟨964, by omega⟩) := by
  have hm : certMode (⟨964, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨964, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨964, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨964, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨964, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_965 :
    ((certNum ⟨965, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨965, by omega⟩) ⟨965, by omega⟩ (certE ⟨965, by omega⟩) := by
  have hm : certMode (⟨965, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨965, by omega⟩ : Fin 1104) = 203776798339215356013773999631 := by decide +kernel
  have he : certE (⟨965, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨965, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨965, by omega⟩ : Fin 1104)).2.2 = 21054416982 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_966 :
    ((certNum ⟨966, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨966, by omega⟩) ⟨966, by omega⟩ (certE ⟨966, by omega⟩) := by
  have hm : certMode (⟨966, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨966, by omega⟩ : Fin 1104) = 39822007901910008609477255289 := by decide +kernel
  have he : certE (⟨966, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -37 else if j.val = 1 then -2 else if j.val = 2 then 4 else 8)) := by decide +kernel
  have hp : parent2 (⟨966, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨966, by omega⟩ : Fin 1104)).2.2 = 2912785116 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_967 :
    ((certNum ⟨967, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨967, by omega⟩) ⟨967, by omega⟩ (certE ⟨967, by omega⟩) := by
  have hm : certMode (⟨967, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨967, by omega⟩ : Fin 1104) = 203779346060624120168919298341 := by decide +kernel
  have he : certE (⟨967, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨967, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨967, by omega⟩ : Fin 1104)).2.2 = 21054750658 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_968 :
    ((certNum ⟨968, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨968, by omega⟩) ⟨968, by omega⟩ (certE ⟨968, by omega⟩) := by
  have hm : certMode (⟨968, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨968, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨968, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨968, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨968, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_969 :
    ((certNum ⟨969, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨969, by omega⟩) ⟨969, by omega⟩ (certE ⟨969, by omega⟩) := by
  have hm : certMode (⟨969, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨969, by omega⟩ : Fin 1104) = 203776131123479274615157456799 := by decide +kernel
  have he : certE (⟨969, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨969, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨969, by omega⟩ : Fin 1104)).2.2 = 21054329594 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_970 :
    ((certNum ⟨970, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨970, by omega⟩) ⟨970, by omega⟩ (certE ⟨970, by omega⟩) := by
  have hm : certMode (⟨970, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨970, by omega⟩ : Fin 1104) = 203947242752456275700210217279 := by decide +kernel
  have he : certE (⟨970, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨970, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨970, by omega⟩ : Fin 1104)).2.2 = 21076743945 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_971 :
    ((certNum ⟨971, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨971, by omega⟩) ⟨971, by omega⟩ (certE ⟨971, by omega⟩) := by
  have hm : certMode (⟨971, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨971, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨971, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨971, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨971, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_972 :
    ((certNum ⟨972, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨972, by omega⟩) ⟨972, by omega⟩ (certE ⟨972, by omega⟩) := by
  have hm : certMode (⟨972, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨972, by omega⟩ : Fin 1104) = 203947221975964927368274482528 := by decide +kernel
  have he : certE (⟨972, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨972, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨972, by omega⟩ : Fin 1104)).2.2 = 21076741223 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_973 :
    ((certNum ⟨973, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨973, by omega⟩) ⟨973, by omega⟩ (certE ⟨973, by omega⟩) := by
  have hm : certMode (⟨973, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨973, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨973, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨973, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨973, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_974 :
    ((certNum ⟨974, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨974, by omega⟩) ⟨974, by omega⟩ (certE ⟨974, by omega⟩) := by
  have hm : certMode (⟨974, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨974, by omega⟩ : Fin 1104) = 177447638881352516197071748502 := by decide +kernel
  have he : certE (⟨974, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 17 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨974, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨974, by omega⟩ : Fin 1104)).2.2 = 17683919351 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_975 :
    ((certNum ⟨975, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨975, by omega⟩) ⟨975, by omega⟩ (certE ⟨975, by omega⟩) := by
  have hm : certMode (⟨975, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨975, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨975, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨975, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨975, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_976 :
    ((certNum ⟨976, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨976, by omega⟩) ⟨976, by omega⟩ (certE ⟨976, by omega⟩) := by
  have hm : certMode (⟨976, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨976, by omega⟩ : Fin 1104) = 203774807549245617586570354180 := by decide +kernel
  have he : certE (⟨976, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨976, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨976, by omega⟩ : Fin 1104)).2.2 = 21054156238 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_977 :
    ((certNum ⟨977, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨977, by omega⟩) ⟨977, by omega⟩ (certE ⟨977, by omega⟩) := by
  have hm : certMode (⟨977, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨977, by omega⟩ : Fin 1104) = 177418430325002809316521734095 := by decide +kernel
  have he : certE (⟨977, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 18 else if j.val = 1 then 5 else if j.val = 2 then -4 else -8)) := by decide +kernel
  have hp : parent2 (⟨977, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨977, by omega⟩ : Fin 1104)).2.2 = 17680267501 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_978 :
    ((certNum ⟨978, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨978, by omega⟩) ⟨978, by omega⟩ (certE ⟨978, by omega⟩) := by
  have hm : certMode (⟨978, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨978, by omega⟩ : Fin 1104) = 203879371111605512763194842341 := by decide +kernel
  have he : certE (⟨978, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨978, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨978, by omega⟩ : Fin 1104)).2.2 = 21067852466 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_979 :
    ((certNum ⟨979, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨979, by omega⟩) ⟨979, by omega⟩ (certE ⟨979, by omega⟩) := by
  have hm : certMode (⟨979, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨979, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨979, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨979, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨979, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_980 :
    ((certNum ⟨980, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨980, by omega⟩) ⟨980, by omega⟩ (certE ⟨980, by omega⟩) := by
  have hm : certMode (⟨980, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨980, by omega⟩ : Fin 1104) = 203947296991151605711841055967 := by decide +kernel
  have he : certE (⟨980, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨980, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨980, by omega⟩ : Fin 1104)).2.2 = 21076751051 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_981 :
    ((certNum ⟨981, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨981, by omega⟩) ⟨981, by omega⟩ (certE ⟨981, by omega⟩) := by
  have hm : certMode (⟨981, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨981, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨981, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨981, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨981, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_982 :
    ((certNum ⟨982, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨982, by omega⟩) ⟨982, by omega⟩ (certE ⟨982, by omega⟩) := by
  have hm : certMode (⟨982, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨982, by omega⟩ : Fin 1104) = 3056333440469904528600737 := by decide +kernel
  have he : certE (⟨982, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -20 else if j.val = 1 then -4 else if j.val = 2 then -6 else 6)) := by decide +kernel
  have hp : parent2 (⟨982, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨982, by omega⟩ : Fin 1104)).2.2 = 88648 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_983 :
    ((certNum ⟨983, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨983, by omega⟩) ⟨983, by omega⟩ (certE ⟨983, by omega⟩) := by
  have hm : certMode (⟨983, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨983, by omega⟩ : Fin 1104) = 203947297105643634244588831038 := by decide +kernel
  have he : certE (⟨983, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨983, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨983, by omega⟩ : Fin 1104)).2.2 = 21076751066 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_984 :
    ((certNum ⟨984, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨984, by omega⟩) ⟨984, by omega⟩ (certE ⟨984, by omega⟩) := by
  have hm : certMode (⟨984, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨984, by omega⟩ : Fin 1104) = 3077016840399653821478666 := by decide +kernel
  have he : certE (⟨984, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -9 else if j.val = 1 then 0 else if j.val = 2 then -5 else -1)) := by decide +kernel
  have hp : parent2 (⟨984, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨984, by omega⟩ : Fin 1104)).2.2 = 89285 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_985 :
    ((certNum ⟨985, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨985, by omega⟩) ⟨985, by omega⟩ (certE ⟨985, by omega⟩) := by
  have hm : certMode (⟨985, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨985, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨985, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨985, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨985, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_986 :
    ((certNum ⟨986, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨986, by omega⟩) ⟨986, by omega⟩ (certE ⟨986, by omega⟩) := by
  have hm : certMode (⟨986, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨986, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨986, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨986, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨986, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_987 :
    ((certNum ⟨987, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨987, by omega⟩) ⟨987, by omega⟩ (certE ⟨987, by omega⟩) := by
  have hm : certMode (⟨987, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨987, by omega⟩ : Fin 1104) = 203308738992409987119621363008 := by decide +kernel
  have he : certE (⟨987, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨987, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨987, by omega⟩ : Fin 1104)).2.2 = 20993139289 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_988 :
    ((certNum ⟨988, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨988, by omega⟩) ⟨988, by omega⟩ (certE ⟨988, by omega⟩) := by
  have hm : certMode (⟨988, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨988, by omega⟩ : Fin 1104) = 190492986545192577533888780590 := by decide +kernel
  have he : certE (⟨988, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -8 else 1)) := by decide +kernel
  have hp : parent2 (⟨988, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨988, by omega⟩ : Fin 1104)).2.2 = 19334351199 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_989 :
    ((certNum ⟨989, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨989, by omega⟩) ⟨989, by omega⟩ (certE ⟨989, by omega⟩) := by
  have hm : certMode (⟨989, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨989, by omega⟩ : Fin 1104) = 91294230838885569629905824286 := by decide +kernel
  have he : certE (⟨989, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -6 else if j.val = 1 then 7 else if j.val = 2 then -4 else -1)) := by decide +kernel
  have hp : parent2 (⟨989, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨989, by omega⟩ : Fin 1104)).2.2 = 7810325780 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_990 :
    ((certNum ⟨990, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨990, by omega⟩) ⟨990, by omega⟩ (certE ⟨990, by omega⟩) := by
  have hm : certMode (⟨990, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨990, by omega⟩ : Fin 1104) = 203308751768703821835923601964 := by decide +kernel
  have he : certE (⟨990, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨990, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨990, by omega⟩ : Fin 1104)).2.2 = 20993140961 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_991 :
    ((certNum ⟨991, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨991, by omega⟩) ⟨991, by omega⟩ (certE ⟨991, by omega⟩) := by
  have hm : certMode (⟨991, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨991, by omega⟩ : Fin 1104) = 180784959521799030932018852643 := by decide +kernel
  have he : certE (⟨991, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hp : parent2 (⟨991, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨991, by omega⟩ : Fin 1104)).2.2 = 18102453834 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_992 :
    ((certNum ⟨992, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨992, by omega⟩) ⟨992, by omega⟩ (certE ⟨992, by omega⟩) := by
  have hm : certMode (⟨992, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨992, by omega⟩ : Fin 1104) = 203947319599509975199327833567 := by decide +kernel
  have he : certE (⟨992, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨992, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨992, by omega⟩ : Fin 1104)).2.2 = 21076754013 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_993 :
    ((certNum ⟨993, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨993, by omega⟩) ⟨993, by omega⟩ (certE ⟨993, by omega⟩) := by
  have hm : certMode (⟨993, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨993, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨993, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨993, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨993, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_994 :
    ((certNum ⟨994, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨994, by omega⟩) ⟨994, by omega⟩ (certE ⟨994, by omega⟩) := by
  have hm : certMode (⟨994, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨994, by omega⟩ : Fin 1104) = 190579371213131309700809219623 := by decide +kernel
  have he : certE (⟨994, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -5 else -3)) := by decide +kernel
  have hp : parent2 (⟨994, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨994, by omega⟩ : Fin 1104)).2.2 = 19345408660 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_995 :
    ((certNum ⟨995, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨995, by omega⟩) ⟨995, by omega⟩ (certE ⟨995, by omega⟩) := by
  have hm : certMode (⟨995, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨995, by omega⟩ : Fin 1104) = 203947317256239961610213893842 := by decide +kernel
  have he : certE (⟨995, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨995, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨995, by omega⟩ : Fin 1104)).2.2 = 21076753706 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_996 :
    ((certNum ⟨996, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨996, by omega⟩) ⟨996, by omega⟩ (certE ⟨996, by omega⟩) := by
  have hm : certMode (⟨996, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨996, by omega⟩ : Fin 1104) = 89941575094276572525337380110 := by decide +kernel
  have he : certE (⟨996, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then 18 else if j.val = 1 then -7 else if j.val = 2 then -6 else 0)) := by decide +kernel
  have hp : parent2 (⟨996, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨996, by omega⟩ : Fin 1104)).2.2 = 7670753034 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_997 :
    ((certNum ⟨997, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨997, by omega⟩) ⟨997, by omega⟩ (certE ⟨997, by omega⟩) := by
  have hm : certMode (⟨997, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨997, by omega⟩ : Fin 1104) = 181064714293807136510215513141 := by decide +kernel
  have he : certE (⟨997, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨997, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨997, by omega⟩ : Fin 1104)).2.2 = 18137653027 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_998 :
    ((certNum ⟨998, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨998, by omega⟩) ⟨998, by omega⟩ (certE ⟨998, by omega⟩) := by
  have hm : certMode (⟨998, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨998, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨998, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨998, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨998, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_999 :
    ((certNum ⟨999, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨999, by omega⟩) ⟨999, by omega⟩ (certE ⟨999, by omega⟩) := by
  have hm : certMode (⟨999, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨999, by omega⟩ : Fin 1104) = 169641798500621958836631664038 := by decide +kernel
  have he : certE (⟨999, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then -38 else if j.val = 1 then 7 else if j.val = 2 then 3 else 5)) := by decide +kernel
  have hp : parent2 (⟨999, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨999, by omega⟩ : Fin 1104)).2.2 = 16714973139 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1000 :
    ((certNum ⟨1000, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1000, by omega⟩) ⟨1000, by omega⟩ (certE ⟨1000, by omega⟩) := by
  have hm : certMode (⟨1000, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1000, by omega⟩ : Fin 1104) = 203774797051087480844014076782 := by decide +kernel
  have he : certE (⟨1000, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨1000, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1000, by omega⟩ : Fin 1104)).2.2 = 21054154863 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1001 :
    ((certNum ⟨1001, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1001, by omega⟩) ⟨1001, by omega⟩ (certE ⟨1001, by omega⟩) := by
  have hm : certMode (⟨1001, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1001, by omega⟩ : Fin 1104) = 204038821449979936013005062604 := by decide +kernel
  have he : certE (⟨1001, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨1001, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1001, by omega⟩ : Fin 1104)).2.2 = 21088742882 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1002 :
    ((certNum ⟨1002, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1002, by omega⟩) ⟨1002, by omega⟩ (certE ⟨1002, by omega⟩) := by
  have hm : certMode (⟨1002, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1002, by omega⟩ : Fin 1104) = 53317504723938649039631160738 := by decide +kernel
  have he : certE (⟨1002, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -26 else if j.val = 1 then 2 else if j.val = 2 then 4 else 2)) := by decide +kernel
  have hp : parent2 (⟨1002, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1002, by omega⟩ : Fin 1104)).2.2 = 4107081173 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1003 :
    ((certNum ⟨1003, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1003, by omega⟩) ⟨1003, by omega⟩ (certE ⟨1003, by omega⟩) := by
  have hm : certMode (⟨1003, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1003, by omega⟩ : Fin 1104) = 203774826674980022769058286690 := by decide +kernel
  have he : certE (⟨1003, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨1003, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1003, by omega⟩ : Fin 1104)).2.2 = 21054158743 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1004 :
    ((certNum ⟨1004, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1004, by omega⟩) ⟨1004, by omega⟩ (certE ⟨1004, by omega⟩) := by
  have hm : certMode (⟨1004, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1004, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1004, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1004, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1004, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1005 :
    ((certNum ⟨1005, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1005, by omega⟩) ⟨1005, by omega⟩ (certE ⟨1005, by omega⟩) := by
  have hm : certMode (⟨1005, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1005, by omega⟩ : Fin 1104) = 196698879898701794288778819242 := by decide +kernel
  have he : certE (⟨1005, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -32 else if j.val = 1 then 1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨1005, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1005, by omega⟩ : Fin 1104)).2.2 = 20133003359 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1006 :
    ((certNum ⟨1006, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1006, by omega⟩) ⟨1006, by omega⟩ (certE ⟨1006, by omega⟩) := by
  have hm : certMode (⟨1006, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1006, by omega⟩ : Fin 1104) = 3338186911378000011988416 := by decide +kernel
  have he : certE (⟨1006, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -25 else if j.val = 1 then -1 else if j.val = 2 then -1 else 2)) := by decide +kernel
  have hp : parent2 (⟨1006, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1006, by omega⟩ : Fin 1104)).2.2 = 97352 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1007 :
    ((certNum ⟨1007, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1007, by omega⟩) ⟨1007, by omega⟩ (certE ⟨1007, by omega⟩) := by
  have hm : certMode (⟨1007, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1007, by omega⟩ : Fin 1104) = 3988971127827937885704117 := by decide +kernel
  have he : certE (⟨1007, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -8 else if j.val = 1 then -6 else if j.val = 2 then -6 else 3)) := by decide +kernel
  have hp : parent2 (⟨1007, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1007, by omega⟩ : Fin 1104)).2.2 = 117629 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1008 :
    ((certNum ⟨1008, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1008, by omega⟩) ⟨1008, by omega⟩ (certE ⟨1008, by omega⟩) := by
  have hm : certMode (⟨1008, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1008, by omega⟩ : Fin 1104) = 196698879821416520920740726892 := by decide +kernel
  have he : certE (⟨1008, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -32 else if j.val = 1 then 1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨1008, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1008, by omega⟩ : Fin 1104)).2.2 = 20133003349 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1009 :
    ((certNum ⟨1009, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1009, by omega⟩) ⟨1009, by omega⟩ (certE ⟨1009, by omega⟩) := by
  have hm : certMode (⟨1009, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨1009, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨1009, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨1009, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨1009, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1010 :
    ((certNum ⟨1010, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1010, by omega⟩) ⟨1010, by omega⟩ (certE ⟨1010, by omega⟩) := by
  have hm : certMode (⟨1010, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1010, by omega⟩ : Fin 1104) = 203947269245915376846521746133 := by decide +kernel
  have he : certE (⟨1010, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨1010, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1010, by omega⟩ : Fin 1104)).2.2 = 21076747416 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1011 :
    ((certNum ⟨1011, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1011, by omega⟩) ⟨1011, by omega⟩ (certE ⟨1011, by omega⟩) := by
  have hm : certMode (⟨1011, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨1011, by omega⟩ : Fin 1104) = 53315916449044955301531146545 := by decide +kernel
  have he : certE (⟨1011, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 22 else if j.val = 1 then 2 else if j.val = 2 then -7 else -6)) := by decide +kernel
  have hp : parent2 (⟨1011, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨1011, by omega⟩ : Fin 1104)).2.2 = 4106936436 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨920 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨920 + j.val, by omega⟩) ⟨920 + j.val, by omega⟩
        (certE ⟨920 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_920
  | ⟨1, _⟩ => exact MME.L2Cert.cert_921
  | ⟨2, _⟩ => exact MME.L2Cert.cert_922
  | ⟨3, _⟩ => exact MME.L2Cert.cert_923
  | ⟨4, _⟩ => exact MME.L2Cert.cert_924
  | ⟨5, _⟩ => exact MME.L2Cert.cert_925
  | ⟨6, _⟩ => exact MME.L2Cert.cert_926
  | ⟨7, _⟩ => exact MME.L2Cert.cert_927
  | ⟨8, _⟩ => exact MME.L2Cert.cert_928
  | ⟨9, _⟩ => exact MME.L2Cert.cert_929
  | ⟨10, _⟩ => exact MME.L2Cert.cert_930
  | ⟨11, _⟩ => exact MME.L2Cert.cert_931
  | ⟨12, _⟩ => exact MME.L2Cert.cert_932
  | ⟨13, _⟩ => exact MME.L2Cert.cert_933
  | ⟨14, _⟩ => exact MME.L2Cert.cert_934
  | ⟨15, _⟩ => exact MME.L2Cert.cert_935
  | ⟨16, _⟩ => exact MME.L2Cert.cert_936
  | ⟨17, _⟩ => exact MME.L2Cert.cert_937
  | ⟨18, _⟩ => exact MME.L2Cert.cert_938
  | ⟨19, _⟩ => exact MME.L2Cert.cert_939
  | ⟨20, _⟩ => exact MME.L2Cert.cert_940
  | ⟨21, _⟩ => exact MME.L2Cert.cert_941
  | ⟨22, _⟩ => exact MME.L2Cert.cert_942
  | ⟨23, _⟩ => exact MME.L2Cert.cert_943
  | ⟨24, _⟩ => exact MME.L2Cert.cert_944
  | ⟨25, _⟩ => exact MME.L2Cert.cert_945
  | ⟨26, _⟩ => exact MME.L2Cert.cert_946
  | ⟨27, _⟩ => exact MME.L2Cert.cert_947
  | ⟨28, _⟩ => exact MME.L2Cert.cert_948
  | ⟨29, _⟩ => exact MME.L2Cert.cert_949
  | ⟨30, _⟩ => exact MME.L2Cert.cert_950
  | ⟨31, _⟩ => exact MME.L2Cert.cert_951
  | ⟨32, _⟩ => exact MME.L2Cert.cert_952
  | ⟨33, _⟩ => exact MME.L2Cert.cert_953
  | ⟨34, _⟩ => exact MME.L2Cert.cert_954
  | ⟨35, _⟩ => exact MME.L2Cert.cert_955
  | ⟨36, _⟩ => exact MME.L2Cert.cert_956
  | ⟨37, _⟩ => exact MME.L2Cert.cert_957
  | ⟨38, _⟩ => exact MME.L2Cert.cert_958
  | ⟨39, _⟩ => exact MME.L2Cert.cert_959
  | ⟨40, _⟩ => exact MME.L2Cert.cert_960
  | ⟨41, _⟩ => exact MME.L2Cert.cert_961
  | ⟨42, _⟩ => exact MME.L2Cert.cert_962
  | ⟨43, _⟩ => exact MME.L2Cert.cert_963
  | ⟨44, _⟩ => exact MME.L2Cert.cert_964
  | ⟨45, _⟩ => exact MME.L2Cert.cert_965
  | ⟨46, _⟩ => exact MME.L2Cert.cert_966
  | ⟨47, _⟩ => exact MME.L2Cert.cert_967
  | ⟨48, _⟩ => exact MME.L2Cert.cert_968
  | ⟨49, _⟩ => exact MME.L2Cert.cert_969
  | ⟨50, _⟩ => exact MME.L2Cert.cert_970
  | ⟨51, _⟩ => exact MME.L2Cert.cert_971
  | ⟨52, _⟩ => exact MME.L2Cert.cert_972
  | ⟨53, _⟩ => exact MME.L2Cert.cert_973
  | ⟨54, _⟩ => exact MME.L2Cert.cert_974
  | ⟨55, _⟩ => exact MME.L2Cert.cert_975
  | ⟨56, _⟩ => exact MME.L2Cert.cert_976
  | ⟨57, _⟩ => exact MME.L2Cert.cert_977
  | ⟨58, _⟩ => exact MME.L2Cert.cert_978
  | ⟨59, _⟩ => exact MME.L2Cert.cert_979
  | ⟨60, _⟩ => exact MME.L2Cert.cert_980
  | ⟨61, _⟩ => exact MME.L2Cert.cert_981
  | ⟨62, _⟩ => exact MME.L2Cert.cert_982
  | ⟨63, _⟩ => exact MME.L2Cert.cert_983
  | ⟨64, _⟩ => exact MME.L2Cert.cert_984
  | ⟨65, _⟩ => exact MME.L2Cert.cert_985
  | ⟨66, _⟩ => exact MME.L2Cert.cert_986
  | ⟨67, _⟩ => exact MME.L2Cert.cert_987
  | ⟨68, _⟩ => exact MME.L2Cert.cert_988
  | ⟨69, _⟩ => exact MME.L2Cert.cert_989
  | ⟨70, _⟩ => exact MME.L2Cert.cert_990
  | ⟨71, _⟩ => exact MME.L2Cert.cert_991
  | ⟨72, _⟩ => exact MME.L2Cert.cert_992
  | ⟨73, _⟩ => exact MME.L2Cert.cert_993
  | ⟨74, _⟩ => exact MME.L2Cert.cert_994
  | ⟨75, _⟩ => exact MME.L2Cert.cert_995
  | ⟨76, _⟩ => exact MME.L2Cert.cert_996
  | ⟨77, _⟩ => exact MME.L2Cert.cert_997
  | ⟨78, _⟩ => exact MME.L2Cert.cert_998
  | ⟨79, _⟩ => exact MME.L2Cert.cert_999
  | ⟨80, _⟩ => exact MME.L2Cert.cert_1000
  | ⟨81, _⟩ => exact MME.L2Cert.cert_1001
  | ⟨82, _⟩ => exact MME.L2Cert.cert_1002
  | ⟨83, _⟩ => exact MME.L2Cert.cert_1003
  | ⟨84, _⟩ => exact MME.L2Cert.cert_1004
  | ⟨85, _⟩ => exact MME.L2Cert.cert_1005
  | ⟨86, _⟩ => exact MME.L2Cert.cert_1006
  | ⟨87, _⟩ => exact MME.L2Cert.cert_1007
  | ⟨88, _⟩ => exact MME.L2Cert.cert_1008
  | ⟨89, _⟩ => exact MME.L2Cert.cert_1009
  | ⟨90, _⟩ => exact MME.L2Cert.cert_1010
  | ⟨91, _⟩ => exact MME.L2Cert.cert_1011
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
