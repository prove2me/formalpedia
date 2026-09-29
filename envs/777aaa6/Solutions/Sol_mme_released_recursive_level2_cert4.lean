-- Prove2me | solution 1 for mme_released_recursive_level2_cert4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:19:48.919826+00:00
-- url     : https://prove2.me/submissions/a829f0d7-317b-470c-8e83-be54d076e83e

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

theorem cert_368 :
    ((certNum ⟨368, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨368, by omega⟩) ⟨368, by omega⟩ (certE ⟨368, by omega⟩) := by
  have hm : certMode (⟨368, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨368, by omega⟩ : Fin 1104) = 21411440904742419694508578 := by decide +kernel
  have he : certE (⟨368, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -12 else if j.val = 1 then -6 else if j.val = 2 then -8 else 7)) := by decide +kernel
  have hp : parent2 (⟨368, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨368, by omega⟩ : Fin 1104)).2.2 = 706013 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_369 :
    ((certNum ⟨369, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨369, by omega⟩) ⟨369, by omega⟩ (certE ⟨369, by omega⟩) := by
  have hm : certMode (⟨369, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨369, by omega⟩ : Fin 1104) = 21755946763811472311603176 := by decide +kernel
  have he : certE (⟨369, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then 4 else -5)) := by decide +kernel
  have hp : parent2 (⟨369, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨369, by omega⟩ : Fin 1104)).2.2 = 718182 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_370 :
    ((certNum ⟨370, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨370, by omega⟩) ⟨370, by omega⟩ (certE ⟨370, by omega⟩) := by
  have hm : certMode (⟨370, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨370, by omega⟩ : Fin 1104) = 21411837487490129929216862 := by decide +kernel
  have he : certE (⟨370, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -12 else if j.val = 1 then -6 else if j.val = 2 then -8 else 7)) := by decide +kernel
  have hp : parent2 (⟨370, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨370, by omega⟩ : Fin 1104)).2.2 = 706027 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_371 :
    ((certNum ⟨371, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨371, by omega⟩) ⟨371, by omega⟩ (certE ⟨371, by omega⟩) := by
  have hm : certMode (⟨371, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨371, by omega⟩ : Fin 1104) = 21757248243895812362103218 := by decide +kernel
  have he : certE (⟨371, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -22 else if j.val = 1 then -7 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hp : parent2 (⟨371, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨371, by omega⟩ : Fin 1104)).2.2 = 718228 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_372 :
    ((certNum ⟨372, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨372, by omega⟩) ⟨372, by omega⟩ (certE ⟨372, by omega⟩) := by
  have hm : certMode (⟨372, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨372, by omega⟩ : Fin 1104) = 16604166406807192943082861 := by decide +kernel
  have he : certE (⟨372, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -8 else if j.val = 1 then 4 else if j.val = 2 then -1 else -6)) := by decide +kernel
  have hp : parent2 (⟨372, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨372, by omega⟩ : Fin 1104)).2.2 = 537850 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_373 :
    ((certNum ⟨373, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨373, by omega⟩) ⟨373, by omega⟩ (certE ⟨373, by omega⟩) := by
  have hm : certMode (⟨373, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨373, by omega⟩ : Fin 1104) = 16604195278289476008253654 := by decide +kernel
  have he : certE (⟨373, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -8 else if j.val = 1 then 4 else if j.val = 2 then -1 else -6)) := by decide +kernel
  have hp : parent2 (⟨373, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨373, by omega⟩ : Fin 1104)).2.2 = 537851 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_374 :
    ((certNum ⟨374, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨374, by omega⟩) ⟨374, by omega⟩ (certE ⟨374, by omega⟩) := by
  have hm : certMode (⟨374, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨374, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨374, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨374, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨374, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_375 :
    ((certNum ⟨375, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨375, by omega⟩) ⟨375, by omega⟩ (certE ⟨375, by omega⟩) := by
  have hm : certMode (⟨375, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨375, by omega⟩ : Fin 1104) = 203944608957916837959388854220 := by decide +kernel
  have he : certE (⟨375, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨375, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨375, by omega⟩ : Fin 1104)).2.2 = 21076398884 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_376 :
    ((certNum ⟨376, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨376, by omega⟩) ⟨376, by omega⟩ (certE ⟨376, by omega⟩) := by
  have hm : certMode (⟨376, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨376, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨376, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨376, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨376, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_377 :
    ((certNum ⟨377, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨377, by omega⟩) ⟨377, by omega⟩ (certE ⟨377, by omega⟩) := by
  have hm : certMode (⟨377, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨377, by omega⟩ : Fin 1104) = 203944189279433663525877766899 := by decide +kernel
  have he : certE (⟨377, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨377, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨377, by omega⟩ : Fin 1104)).2.2 = 21076343901 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_378 :
    ((certNum ⟨378, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨378, by omega⟩) ⟨378, by omega⟩ (certE ⟨378, by omega⟩) := by
  have hm : certMode (⟨378, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨378, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨378, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨378, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨378, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_379 :
    ((certNum ⟨379, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨379, by omega⟩) ⟨379, by omega⟩ (certE ⟨379, by omega⟩) := by
  have hm : certMode (⟨379, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨379, by omega⟩ : Fin 1104) = 203942523894232652354743265599 := by decide +kernel
  have he : certE (⟨379, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨379, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨379, by omega⟩ : Fin 1104)).2.2 = 21076125716 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_380 :
    ((certNum ⟨380, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨380, by omega⟩) ⟨380, by omega⟩ (certE ⟨380, by omega⟩) := by
  have hm : certMode (⟨380, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨380, by omega⟩ : Fin 1104) = 5013371908165433263891151499 := by decide +kernel
  have he : certE (⟨380, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -5 else if j.val = 1 then -2 else if j.val = 2 then -4 else 2)) := by decide +kernel
  have hp : parent2 (⟨380, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨380, by omega⟩ : Fin 1104)).2.2 = 272209549 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_381 :
    ((certNum ⟨381, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨381, by omega⟩) ⟨381, by omega⟩ (certE ⟨381, by omega⟩) := by
  have hm : certMode (⟨381, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨381, by omega⟩ : Fin 1104) = 203946048384233923135686958580 := by decide +kernel
  have he : certE (⟨381, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨381, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨381, by omega⟩ : Fin 1104)).2.2 = 21076587467 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_382 :
    ((certNum ⟨382, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨382, by omega⟩) ⟨382, by omega⟩ (certE ⟨382, by omega⟩) := by
  have hm : certMode (⟨382, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨382, by omega⟩ : Fin 1104) = 5012946083951464774644495801 := by decide +kernel
  have he : certE (⟨382, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -1 else if j.val = 1 then -8 else if j.val = 2 then 2 else -1)) := by decide +kernel
  have hp : parent2 (⟨382, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨382, by omega⟩ : Fin 1104)).2.2 = 272183611 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_383 :
    ((certNum ⟨383, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨383, by omega⟩) ⟨383, by omega⟩ (certE ⟨383, by omega⟩) := by
  have hm : certMode (⟨383, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨383, by omega⟩ : Fin 1104) = 203946189759557137626468391595 := by decide +kernel
  have he : certE (⟨383, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨383, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨383, by omega⟩ : Fin 1104)).2.2 = 21076605989 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_384 :
    ((certNum ⟨384, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨384, by omega⟩) ⟨384, by omega⟩ (certE ⟨384, by omega⟩) := by
  have hm : certMode (⟨384, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨384, by omega⟩ : Fin 1104) = 10480824845034993237983166763 := by decide +kernel
  have he : certE (⟨384, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -17 else if j.val = 1 then 2 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨384, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨384, by omega⟩ : Fin 1104)).2.2 = 625637903 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_385 :
    ((certNum ⟨385, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨385, by omega⟩) ⟨385, by omega⟩ (certE ⟨385, by omega⟩) := by
  have hm : certMode (⟨385, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨385, by omega⟩ : Fin 1104) = 203946067519748930794913420261 := by decide +kernel
  have he : certE (⟨385, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨385, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨385, by omega⟩ : Fin 1104)).2.2 = 21076589974 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_386 :
    ((certNum ⟨386, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨386, by omega⟩) ⟨386, by omega⟩ (certE ⟨386, by omega⟩) := by
  have hm : certMode (⟨386, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨386, by omega⟩ : Fin 1104) = 202769499351397958528728182837 := by decide +kernel
  have he : certE (⟨386, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨386, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨386, by omega⟩ : Fin 1104)).2.2 = 20922602514 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_387 :
    ((certNum ⟨387, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨387, by omega⟩) ⟨387, by omega⟩ (certE ⟨387, by omega⟩) := by
  have hm : certMode (⟨387, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨387, by omega⟩ : Fin 1104) = 15884651730168857456204213127 := by decide +kernel
  have he : certE (⟨387, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -14 else if j.val = 1 then -6 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨387, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨387, by omega⟩ : Fin 1104)).2.2 = 1005152886 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_388 :
    ((certNum ⟨388, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨388, by omega⟩) ⟨388, by omega⟩ (certE ⟨388, by omega⟩) := by
  have hm : certMode (⟨388, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨388, by omega⟩ : Fin 1104) = 202769579598560293295261978885 := by decide +kernel
  have he : certE (⟨388, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨388, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨388, by omega⟩ : Fin 1104)).2.2 = 20922613006 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_389 :
    ((certNum ⟨389, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨389, by omega⟩) ⟨389, by omega⟩ (certE ⟨389, by omega⟩) := by
  have hm : certMode (⟨389, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨389, by omega⟩ : Fin 1104) = 15885553214124860583320139663 := by decide +kernel
  have he : certE (⟨389, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -18 else if j.val = 1 then 0 else if j.val = 2 then -5 else 7)) := by decide +kernel
  have hp : parent2 (⟨389, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨389, by omega⟩ : Fin 1104)).2.2 = 1005218206 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_390 :
    ((certNum ⟨390, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨390, by omega⟩) ⟨390, by omega⟩ (certE ⟨390, by omega⟩) := by
  have hm : certMode (⟨390, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨390, by omega⟩ : Fin 1104) = 202769422316548946088049314392 := by decide +kernel
  have he : certE (⟨390, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨390, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨390, by omega⟩ : Fin 1104)).2.2 = 20922592442 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_391 :
    ((certNum ⟨391, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨391, by omega⟩) ⟨391, by omega⟩ (certE ⟨391, by omega⟩) := by
  have hm : certMode (⟨391, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨391, by omega⟩ : Fin 1104) = 25551992744742083282102412049 := by decide +kernel
  have he : certE (⟨391, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -16 else if j.val = 1 then 7 else if j.val = 2 then 3 else -4)) := by decide +kernel
  have hp : parent2 (⟨391, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨391, by omega⟩ : Fin 1104)).2.2 = 1737369556 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_392 :
    ((certNum ⟨392, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨392, by omega⟩) ⟨392, by omega⟩ (certE ⟨392, by omega⟩) := by
  have hm : certMode (⟨392, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨392, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨392, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨392, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨392, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_393 :
    ((certNum ⟨393, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨393, by omega⟩) ⟨393, by omega⟩ (certE ⟨393, by omega⟩) := by
  have hm : certMode (⟨393, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨393, by omega⟩ : Fin 1104) = 203946063787293169464215169386 := by decide +kernel
  have he : certE (⟨393, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨393, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨393, by omega⟩ : Fin 1104)).2.2 = 21076589485 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_394 :
    ((certNum ⟨394, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨394, by omega⟩) ⟨394, by omega⟩ (certE ⟨394, by omega⟩) := by
  have hm : certMode (⟨394, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨394, by omega⟩ : Fin 1104) = 203775225810830727261993796870 := by decide +kernel
  have he : certE (⟨394, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨394, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨394, by omega⟩ : Fin 1104)).2.2 = 21054211020 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_395 :
    ((certNum ⟨395, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨395, by omega⟩) ⟨395, by omega⟩ (certE ⟨395, by omega⟩) := by
  have hm : certMode (⟨395, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨395, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨395, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨395, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨395, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_396 :
    ((certNum ⟨396, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨396, by omega⟩) ⟨396, by omega⟩ (certE ⟨396, by omega⟩) := by
  have hm : certMode (⟨396, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨396, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨396, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨396, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨396, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_397 :
    ((certNum ⟨397, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨397, by omega⟩) ⟨397, by omega⟩ (certE ⟨397, by omega⟩) := by
  have hm : certMode (⟨397, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨397, by omega⟩ : Fin 1104) = 203946073969493437371182460230 := by decide +kernel
  have he : certE (⟨397, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨397, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨397, by omega⟩ : Fin 1104)).2.2 = 21076590819 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_398 :
    ((certNum ⟨398, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨398, by omega⟩) ⟨398, by omega⟩ (certE ⟨398, by omega⟩) := by
  have hm : certMode (⟨398, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨398, by omega⟩ : Fin 1104) = 203775091083358737781262293496 := by decide +kernel
  have he : certE (⟨398, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨398, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨398, by omega⟩ : Fin 1104)).2.2 = 21054193374 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_399 :
    ((certNum ⟨399, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨399, by omega⟩) ⟨399, by omega⟩ (certE ⟨399, by omega⟩) := by
  have hm : certMode (⟨399, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨399, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨399, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨399, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨399, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_400 :
    ((certNum ⟨400, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨400, by omega⟩) ⟨400, by omega⟩ (certE ⟨400, by omega⟩) := by
  have hm : certMode (⟨400, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨400, by omega⟩ : Fin 1104) = 203775182734083677600333149287 := by decide +kernel
  have he : certE (⟨400, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨400, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨400, by omega⟩ : Fin 1104)).2.2 = 21054205378 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_401 :
    ((certNum ⟨401, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨401, by omega⟩) ⟨401, by omega⟩ (certE ⟨401, by omega⟩) := by
  have hm : certMode (⟨401, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨401, by omega⟩ : Fin 1104) = 39826443479577424746837311504 := by decide +kernel
  have he : certE (⟨401, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -37 else if j.val = 1 then -2 else if j.val = 2 then 4 else 8)) := by decide +kernel
  have hp : parent2 (⟨401, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨401, by omega⟩ : Fin 1104)).2.2 = 2913165353 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_402 :
    ((certNum ⟨402, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨402, by omega⟩) ⟨402, by omega⟩ (certE ⟨402, by omega⟩) := by
  have hm : certMode (⟨402, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨402, by omega⟩ : Fin 1104) = 203941691514862334463757170167 := by decide +kernel
  have he : certE (⟨402, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨402, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨402, by omega⟩ : Fin 1104)).2.2 = 21076016665 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_403 :
    ((certNum ⟨403, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨403, by omega⟩) ⟨403, by omega⟩ (certE ⟨403, by omega⟩) := by
  have hm : certMode (⟨403, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨403, by omega⟩ : Fin 1104) = 203941722832843907072887572058 := by decide +kernel
  have he : certE (⟨403, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨403, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨403, by omega⟩ : Fin 1104)).2.2 = 21076020768 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_404 :
    ((certNum ⟨404, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨404, by omega⟩) ⟨404, by omega⟩ (certE ⟨404, by omega⟩) := by
  have hm : certMode (⟨404, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨404, by omega⟩ : Fin 1104) = 203941687415969544477251730116 := by decide +kernel
  have he : certE (⟨404, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨404, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨404, by omega⟩ : Fin 1104)).2.2 = 21076016128 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_405 :
    ((certNum ⟨405, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨405, by omega⟩) ⟨405, by omega⟩ (certE ⟨405, by omega⟩) := by
  have hm : certMode (⟨405, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨405, by omega⟩ : Fin 1104) = 203941687446501334558013581843 := by decide +kernel
  have he : certE (⟨405, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨405, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨405, by omega⟩ : Fin 1104)).2.2 = 21076016132 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_406 :
    ((certNum ⟨406, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨406, by omega⟩) ⟨406, by omega⟩ (certE ⟨406, by omega⟩) := by
  have hm : certMode (⟨406, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨406, by omega⟩ : Fin 1104) = 203941722809945067268330778196 := by decide +kernel
  have he : certE (⟨406, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨406, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨406, by omega⟩ : Fin 1104)).2.2 = 21076020765 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_407 :
    ((certNum ⟨407, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨407, by omega⟩) ⟨407, by omega⟩ (certE ⟨407, by omega⟩) := by
  have hm : certMode (⟨407, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨407, by omega⟩ : Fin 1104) = 203941691507229387049472009438 := by decide +kernel
  have he : certE (⟨407, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨407, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨407, by omega⟩ : Fin 1104)).2.2 = 21076016664 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_408 :
    ((certNum ⟨408, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨408, by omega⟩) ⟨408, by omega⟩ (certE ⟨408, by omega⟩) := by
  have hm : certMode (⟨408, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨408, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨408, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨408, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨408, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_409 :
    ((certNum ⟨409, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨409, by omega⟩) ⟨409, by omega⟩ (certE ⟨409, by omega⟩) := by
  have hm : certMode (⟨409, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨409, by omega⟩ : Fin 1104) = 203879298470405699583691499686 := by decide +kernel
  have he : certE (⟨409, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨409, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨409, by omega⟩ : Fin 1104)).2.2 = 21067842950 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_410 :
    ((certNum ⟨410, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨410, by omega⟩) ⟨410, by omega⟩ (certE ⟨410, by omega⟩) := by
  have hm : certMode (⟨410, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨410, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨410, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨410, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨410, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_411 :
    ((certNum ⟨411, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨411, by omega⟩) ⟨411, by omega⟩ (certE ⟨411, by omega⟩) := by
  have hm : certMode (⟨411, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨411, by omega⟩ : Fin 1104) = 203880211232028324164757821200 := by decide +kernel
  have he : certE (⟨411, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨411, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨411, by omega⟩ : Fin 1104)).2.2 = 21067962519 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_412 :
    ((certNum ⟨412, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨412, by omega⟩) ⟨412, by omega⟩ (certE ⟨412, by omega⟩) := by
  have hm : certMode (⟨412, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨412, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨412, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨412, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨412, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_413 :
    ((certNum ⟨413, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨413, by omega⟩) ⟨413, by omega⟩ (certE ⟨413, by omega⟩) := by
  have hm : certMode (⟨413, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨413, by omega⟩ : Fin 1104) = 203879042310033125399362738280 := by decide +kernel
  have he : certE (⟨413, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨413, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨413, by omega⟩ : Fin 1104)).2.2 = 21067809393 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_414 :
    ((certNum ⟨414, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨414, by omega⟩) ⟨414, by omega⟩ (certE ⟨414, by omega⟩) := by
  have hm : certMode (⟨414, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨414, by omega⟩ : Fin 1104) = 22924606404367670341414423652 := by decide +kernel
  have he : certE (⟨414, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then -19 else if j.val = 1 then 2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨414, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨414, by omega⟩ : Fin 1104)).2.2 = 1532537704 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_415 :
    ((certNum ⟨415, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨415, by omega⟩) ⟨415, by omega⟩ (certE ⟨415, by omega⟩) := by
  have hm : certMode (⟨415, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨415, by omega⟩ : Fin 1104) = 204038943923747475158433172763 := by decide +kernel
  have he : certE (⟨415, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨415, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨415, by omega⟩ : Fin 1104)).2.2 = 21088758930 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_416 :
    ((certNum ⟨416, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨416, by omega⟩) ⟨416, by omega⟩ (certE ⟨416, by omega⟩) := by
  have hm : certMode (⟨416, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨416, by omega⟩ : Fin 1104) = 203879762347821914860251763855 := by decide +kernel
  have he : certE (⟨416, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨416, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨416, by omega⟩ : Fin 1104)).2.2 = 21067903718 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_417 :
    ((certNum ⟨417, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨417, by omega⟩) ⟨417, by omega⟩ (certE ⟨417, by omega⟩) := by
  have hm : certMode (⟨417, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨417, by omega⟩ : Fin 1104) = 154651668608292104999191581978 := by decide +kernel
  have he : certE (⟨417, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -14 else if j.val = 1 then -3 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hp : parent2 (⟨417, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨417, by omega⟩ : Fin 1104)).2.2 = 14893969038 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_418 :
    ((certNum ⟨418, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨418, by omega⟩) ⟨418, by omega⟩ (certE ⟨418, by omega⟩) := by
  have hm : certMode (⟨418, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨418, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨418, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨418, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨418, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_419 :
    ((certNum ⟨419, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨419, by omega⟩) ⟨419, by omega⟩ (certE ⟨419, by omega⟩) := by
  have hm : certMode (⟨419, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨419, by omega⟩ : Fin 1104) = 203878370408032781916601722736 := by decide +kernel
  have he : certE (⟨419, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨419, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨419, by omega⟩ : Fin 1104)).2.2 = 21067721374 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_420 :
    ((certNum ⟨420, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨420, by omega⟩) ⟨420, by omega⟩ (certE ⟨420, by omega⟩) := by
  have hm : certMode (⟨420, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨420, by omega⟩ : Fin 1104) = 22924327569555144350555089769 := by decide +kernel
  have he : certE (⟨420, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then -19 else if j.val = 1 then 2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨420, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨420, by omega⟩ : Fin 1104)).2.2 = 1532516182 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_421 :
    ((certNum ⟨421, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨421, by omega⟩) ⟨421, by omega⟩ (certE ⟨421, by omega⟩) := by
  have hm : certMode (⟨421, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨421, by omega⟩ : Fin 1104) = 203946054772916176257359885776 := by decide +kernel
  have he : certE (⟨421, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨421, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨421, by omega⟩ : Fin 1104)).2.2 = 21076588304 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_422 :
    ((certNum ⟨422, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨422, by omega⟩) ⟨422, by omega⟩ (certE ⟨422, by omega⟩) := by
  have hm : certMode (⟨422, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨422, by omega⟩ : Fin 1104) = 203972461202802076153249695129 := by decide +kernel
  have he : certE (⟨422, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 1 else if j.val = 1 then -2 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hp : parent2 (⟨422, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨422, by omega⟩ : Fin 1104)).2.2 = 21080047956 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_423 :
    ((certNum ⟨423, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨423, by omega⟩) ⟨423, by omega⟩ (certE ⟨423, by omega⟩) := by
  have hm : certMode (⟨423, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨423, by omega⟩ : Fin 1104) = 154632374752541951612078590426 := by decide +kernel
  have he : certE (⟨423, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -14 else if j.val = 1 then 8 else if j.val = 2 then 4 else -5)) := by decide +kernel
  have hp : parent2 (⟨423, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨423, by omega⟩ : Fin 1104)).2.2 = 14891659264 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_424 :
    ((certNum ⟨424, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨424, by omega⟩) ⟨424, by omega⟩ (certE ⟨424, by omega⟩) := by
  have hm : certMode (⟨424, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨424, by omega⟩ : Fin 1104) = 203946142756582262065814027093 := by decide +kernel
  have he : certE (⟨424, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨424, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨424, by omega⟩ : Fin 1104)).2.2 = 21076599831 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_425 :
    ((certNum ⟨425, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨425, by omega⟩) ⟨425, by omega⟩ (certE ⟨425, by omega⟩) := by
  have hm : certMode (⟨425, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨425, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨425, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨425, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨425, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_426 :
    ((certNum ⟨426, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨426, by omega⟩) ⟨426, by omega⟩ (certE ⟨426, by omega⟩) := by
  have hm : certMode (⟨426, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨426, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨426, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨426, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨426, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_427 :
    ((certNum ⟨427, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨427, by omega⟩) ⟨427, by omega⟩ (certE ⟨427, by omega⟩) := by
  have hm : certMode (⟨427, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨427, by omega⟩ : Fin 1104) = 203946151595401430335487835161 := by decide +kernel
  have he : certE (⟨427, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨427, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨427, by omega⟩ : Fin 1104)).2.2 = 21076600989 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_428 :
    ((certNum ⟨428, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨428, by omega⟩) ⟨428, by omega⟩ (certE ⟨428, by omega⟩) := by
  have hm : certMode (⟨428, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨428, by omega⟩ : Fin 1104) = 190767569535551687786884485807 := by decide +kernel
  have he : certE (⟨428, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨428, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨428, by omega⟩ : Fin 1104)).2.2 = 19369504580 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_429 :
    ((certNum ⟨429, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨429, by omega⟩) ⟨429, by omega⟩ (certE ⟨429, by omega⟩) := by
  have hm : certMode (⟨429, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨429, by omega⟩ : Fin 1104) = 89064928898516806006581207821 := by decide +kernel
  have he : certE (⟨429, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 16 else if j.val = 1 then -8 else if j.val = 2 then 4 else -7)) := by decide +kernel
  have hp : parent2 (⟨429, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨429, by omega⟩ : Fin 1104)).2.2 = 7580579254 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_430 :
    ((certNum ⟨430, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨430, by omega⟩) ⟨430, by omega⟩ (certE ⟨430, by omega⟩) := by
  have hm : certMode (⟨430, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨430, by omega⟩ : Fin 1104) = 203946155694231990731589028989 := by decide +kernel
  have he : certE (⟨430, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨430, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨430, by omega⟩ : Fin 1104)).2.2 = 21076601526 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_431 :
    ((certNum ⟨431, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨431, by omega⟩) ⟨431, by omega⟩ (certE ⟨431, by omega⟩) := by
  have hm : certMode (⟨431, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨431, by omega⟩ : Fin 1104) = 181449066191355560840799504631 := by decide +kernel
  have he : certE (⟨431, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hp : parent2 (⟨431, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨431, by omega⟩ : Fin 1104)).2.2 = 18186042626 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_432 :
    ((certNum ⟨432, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨432, by omega⟩) ⟨432, by omega⟩ (certE ⟨432, by omega⟩) := by
  have hm : certMode (⟨432, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨432, by omega⟩ : Fin 1104) = 202769377603897949842648762388 := by decide +kernel
  have he : certE (⟨432, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨432, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨432, by omega⟩ : Fin 1104)).2.2 = 20922586596 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_433 :
    ((certNum ⟨433, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨433, by omega⟩) ⟨433, by omega⟩ (certE ⟨433, by omega⟩) := by
  have hm : certMode (⟨433, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨433, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨433, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨433, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨433, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_434 :
    ((certNum ⟨434, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨434, by omega⟩) ⟨434, by omega⟩ (certE ⟨434, by omega⟩) := by
  have hm : certMode (⟨434, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨434, by omega⟩ : Fin 1104) = 190642448831067615766987763830 := by decide +kernel
  have he : certE (⟨434, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨434, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨434, by omega⟩ : Fin 1104)).2.2 = 19353483895 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_435 :
    ((certNum ⟨435, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨435, by omega⟩) ⟨435, by omega⟩ (certE ⟨435, by omega⟩) := by
  have hm : certMode (⟨435, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨435, by omega⟩ : Fin 1104) = 202769367821570556902780648922 := by decide +kernel
  have he : certE (⟨435, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨435, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨435, by omega⟩ : Fin 1104)).2.2 = 20922585317 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_436 :
    ((certNum ⟨436, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨436, by omega⟩) ⟨436, by omega⟩ (certE ⟨436, by omega⟩) := by
  have hm : certMode (⟨436, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨436, by omega⟩ : Fin 1104) = 91631814414010778078850391835 := by decide +kernel
  have he : certE (⟨436, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -7 else if j.val = 1 then -8 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hp : parent2 (⟨436, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨436, by omega⟩ : Fin 1104)).2.2 = 7845241478 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_437 :
    ((certNum ⟨437, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨437, by omega⟩) ⟨437, by omega⟩ (certE ⟨437, by omega⟩) := by
  have hm : certMode (⟨437, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨437, by omega⟩ : Fin 1104) = 180940584329407369077951428244 := by decide +kernel
  have he : certE (⟨437, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 14 else if j.val = 1 then -4 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨437, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨437, by omega⟩ : Fin 1104)).2.2 = 18122032534 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_438 :
    ((certNum ⟨438, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨438, by omega⟩) ⟨438, by omega⟩ (certE ⟨438, by omega⟩) := by
  have hm : certMode (⟨438, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨438, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨438, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨438, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨438, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_439 :
    ((certNum ⟨439, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨439, by omega⟩) ⟨439, by omega⟩ (certE ⟨439, by omega⟩) := by
  have hm : certMode (⟨439, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨439, by omega⟩ : Fin 1104) = 177418074376468476344338937402 := by decide +kernel
  have he : certE (⟨439, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 18 else if j.val = 1 then 5 else if j.val = 2 then -4 else -8)) := by decide +kernel
  have hp : parent2 (⟨439, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨439, by omega⟩ : Fin 1104)).2.2 = 17680222999 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_440 :
    ((certNum ⟨440, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨440, by omega⟩) ⟨440, by omega⟩ (certE ⟨440, by omega⟩) := by
  have hm : certMode (⟨440, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨440, by omega⟩ : Fin 1104) = 203879637691525245419154732007 := by decide +kernel
  have he : certE (⟨440, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨440, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨440, by omega⟩ : Fin 1104)).2.2 = 21067887388 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_441 :
    ((certNum ⟨441, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨441, by omega⟩) ⟨441, by omega⟩ (certE ⟨441, by omega⟩) := by
  have hm : certMode (⟨441, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨441, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨441, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨441, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨441, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_442 :
    ((certNum ⟨442, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨442, by omega⟩) ⟨442, by omega⟩ (certE ⟨442, by omega⟩) := by
  have hm : certMode (⟨442, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨442, by omega⟩ : Fin 1104) = 203946190118300177774825095957 := by decide +kernel
  have he : certE (⟨442, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨442, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨442, by omega⟩ : Fin 1104)).2.2 = 21076606036 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_443 :
    ((certNum ⟨443, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨443, by omega⟩) ⟨443, by omega⟩ (certE ⟨443, by omega⟩) := by
  have hm : certMode (⟨443, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨443, by omega⟩ : Fin 1104) = 3065101458640517239153306 := by decide +kernel
  have he : certE (⟨443, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -9 else if j.val = 1 then 8 else if j.val = 2 then -2 else -8)) := by decide +kernel
  have hp : parent2 (⟨443, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨443, by omega⟩ : Fin 1104)).2.2 = 88918 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_444 :
    ((certNum ⟨444, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨444, by omega⟩) ⟨444, by omega⟩ (certE ⟨444, by omega⟩) := by
  have hm : certMode (⟨444, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨444, by omega⟩ : Fin 1104) = 8339174871990664192963302 := by decide +kernel
  have he : certE (⟨444, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -38 else if j.val = 1 then 4 else if j.val = 2 then 3 else 1)) := by decide +kernel
  have hp : parent2 (⟨444, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨444, by omega⟩ : Fin 1104)).2.2 = 257845 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_445 :
    ((certNum ⟨445, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨445, by omega⟩) ⟨445, by omega⟩ (certE ⟨445, by omega⟩) := by
  have hm : certMode (⟨445, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨445, by omega⟩ : Fin 1104) = 203946188309319311289032910867 := by decide +kernel
  have he : certE (⟨445, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨445, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨445, by omega⟩ : Fin 1104)).2.2 = 21076605799 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_446 :
    ((certNum ⟨446, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨446, by omega⟩) ⟨446, by omega⟩ (certE ⟨446, by omega⟩) := by
  have hm : certMode (⟨446, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨446, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨446, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨446, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨446, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_447 :
    ((certNum ⟨447, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨447, by omega⟩) ⟨447, by omega⟩ (certE ⟨447, by omega⟩) := by
  have hm : certMode (⟨447, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨447, by omega⟩ : Fin 1104) = 203776081358612996029995984857 := by decide +kernel
  have he : certE (⟨447, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨447, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨447, by omega⟩ : Fin 1104)).2.2 = 21054323076 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_448 :
    ((certNum ⟨448, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨448, by omega⟩) ⟨448, by omega⟩ (certE ⟨448, by omega⟩) := by
  have hm : certMode (⟨448, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨448, by omega⟩ : Fin 1104) = 177447462203717697177791865741 := by decide +kernel
  have he : certE (⟨448, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 17 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨448, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨448, by omega⟩ : Fin 1104)).2.2 = 17683897261 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_449 :
    ((certNum ⟨449, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨449, by omega⟩) ⟨449, by omega⟩ (certE ⟨449, by omega⟩) := by
  have hm : certMode (⟨449, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨449, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨449, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨449, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨449, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_450 :
    ((certNum ⟨450, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨450, by omega⟩) ⟨450, by omega⟩ (certE ⟨450, by omega⟩) := by
  have hm : certMode (⟨450, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨450, by omega⟩ : Fin 1104) = 39758498425538961724306510789 := by decide +kernel
  have he : certE (⟨450, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -12 else if j.val = 1 then -8 else if j.val = 2 then 7 else 0)) := by decide +kernel
  have hp : parent2 (⟨450, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨450, by omega⟩ : Fin 1104)).2.2 = 2907341807 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_451 :
    ((certNum ⟨451, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨451, by omega⟩) ⟨451, by omega⟩ (certE ⟨451, by omega⟩) := by
  have hm : certMode (⟨451, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨451, by omega⟩ : Fin 1104) = 203880130693814897004253506696 := by decide +kernel
  have he : certE (⟨451, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨451, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨451, by omega⟩ : Fin 1104)).2.2 = 21067951969 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_452 :
    ((certNum ⟨452, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨452, by omega⟩) ⟨452, by omega⟩ (certE ⟨452, by omega⟩) := by
  have hm : certMode (⟨452, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨452, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨452, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨452, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨452, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_453 :
    ((certNum ⟨453, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨453, by omega⟩) ⟨453, by omega⟩ (certE ⟨453, by omega⟩) := by
  have hm : certMode (⟨453, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨453, by omega⟩ : Fin 1104) = 203879588859524932566082894976 := by decide +kernel
  have he : certE (⟨453, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨453, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨453, by omega⟩ : Fin 1104)).2.2 = 21067880991 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_454 :
    ((certNum ⟨454, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨454, by omega⟩) ⟨454, by omega⟩ (certE ⟨454, by omega⟩) := by
  have hm : certMode (⟨454, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨454, by omega⟩ : Fin 1104) = 203946072832201221041697086466 := by decide +kernel
  have he : certE (⟨454, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨454, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨454, by omega⟩ : Fin 1104)).2.2 = 21076590670 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_455 :
    ((certNum ⟨455, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨455, by omega⟩) ⟨455, by omega⟩ (certE ⟨455, by omega⟩) := by
  have hm : certMode (⟨455, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨455, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨455, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨455, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨455, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_456 :
    ((certNum ⟨456, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨456, by omega⟩) ⟨456, by omega⟩ (certE ⟨456, by omega⟩) := by
  have hm : certMode (⟨456, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨456, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨456, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨456, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨456, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_457 :
    ((certNum ⟨457, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨457, by omega⟩) ⟨457, by omega⟩ (certE ⟨457, by omega⟩) := by
  have hm : certMode (⟨457, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨457, by omega⟩ : Fin 1104) = 203879278355904679551712410576 := by decide +kernel
  have he : certE (⟨457, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨457, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨457, by omega⟩ : Fin 1104)).2.2 = 21067840315 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_458 :
    ((certNum ⟨458, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨458, by omega⟩) ⟨458, by omega⟩ (certE ⟨458, by omega⟩) := by
  have hm : certMode (⟨458, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨458, by omega⟩ : Fin 1104) = 203946063375120137700694391708 := by decide +kernel
  have he : certE (⟨458, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨458, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨458, by omega⟩ : Fin 1104)).2.2 = 21076589431 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_459 :
    ((certNum ⟨459, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨459, by omega⟩) ⟨459, by omega⟩ (certE ⟨459, by omega⟩) := by
  have hm : certMode (⟨459, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨459, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨459, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨459, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨459, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨368 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨368 + j.val, by omega⟩) ⟨368 + j.val, by omega⟩
        (certE ⟨368 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_368
  | ⟨1, _⟩ => exact MME.L2Cert.cert_369
  | ⟨2, _⟩ => exact MME.L2Cert.cert_370
  | ⟨3, _⟩ => exact MME.L2Cert.cert_371
  | ⟨4, _⟩ => exact MME.L2Cert.cert_372
  | ⟨5, _⟩ => exact MME.L2Cert.cert_373
  | ⟨6, _⟩ => exact MME.L2Cert.cert_374
  | ⟨7, _⟩ => exact MME.L2Cert.cert_375
  | ⟨8, _⟩ => exact MME.L2Cert.cert_376
  | ⟨9, _⟩ => exact MME.L2Cert.cert_377
  | ⟨10, _⟩ => exact MME.L2Cert.cert_378
  | ⟨11, _⟩ => exact MME.L2Cert.cert_379
  | ⟨12, _⟩ => exact MME.L2Cert.cert_380
  | ⟨13, _⟩ => exact MME.L2Cert.cert_381
  | ⟨14, _⟩ => exact MME.L2Cert.cert_382
  | ⟨15, _⟩ => exact MME.L2Cert.cert_383
  | ⟨16, _⟩ => exact MME.L2Cert.cert_384
  | ⟨17, _⟩ => exact MME.L2Cert.cert_385
  | ⟨18, _⟩ => exact MME.L2Cert.cert_386
  | ⟨19, _⟩ => exact MME.L2Cert.cert_387
  | ⟨20, _⟩ => exact MME.L2Cert.cert_388
  | ⟨21, _⟩ => exact MME.L2Cert.cert_389
  | ⟨22, _⟩ => exact MME.L2Cert.cert_390
  | ⟨23, _⟩ => exact MME.L2Cert.cert_391
  | ⟨24, _⟩ => exact MME.L2Cert.cert_392
  | ⟨25, _⟩ => exact MME.L2Cert.cert_393
  | ⟨26, _⟩ => exact MME.L2Cert.cert_394
  | ⟨27, _⟩ => exact MME.L2Cert.cert_395
  | ⟨28, _⟩ => exact MME.L2Cert.cert_396
  | ⟨29, _⟩ => exact MME.L2Cert.cert_397
  | ⟨30, _⟩ => exact MME.L2Cert.cert_398
  | ⟨31, _⟩ => exact MME.L2Cert.cert_399
  | ⟨32, _⟩ => exact MME.L2Cert.cert_400
  | ⟨33, _⟩ => exact MME.L2Cert.cert_401
  | ⟨34, _⟩ => exact MME.L2Cert.cert_402
  | ⟨35, _⟩ => exact MME.L2Cert.cert_403
  | ⟨36, _⟩ => exact MME.L2Cert.cert_404
  | ⟨37, _⟩ => exact MME.L2Cert.cert_405
  | ⟨38, _⟩ => exact MME.L2Cert.cert_406
  | ⟨39, _⟩ => exact MME.L2Cert.cert_407
  | ⟨40, _⟩ => exact MME.L2Cert.cert_408
  | ⟨41, _⟩ => exact MME.L2Cert.cert_409
  | ⟨42, _⟩ => exact MME.L2Cert.cert_410
  | ⟨43, _⟩ => exact MME.L2Cert.cert_411
  | ⟨44, _⟩ => exact MME.L2Cert.cert_412
  | ⟨45, _⟩ => exact MME.L2Cert.cert_413
  | ⟨46, _⟩ => exact MME.L2Cert.cert_414
  | ⟨47, _⟩ => exact MME.L2Cert.cert_415
  | ⟨48, _⟩ => exact MME.L2Cert.cert_416
  | ⟨49, _⟩ => exact MME.L2Cert.cert_417
  | ⟨50, _⟩ => exact MME.L2Cert.cert_418
  | ⟨51, _⟩ => exact MME.L2Cert.cert_419
  | ⟨52, _⟩ => exact MME.L2Cert.cert_420
  | ⟨53, _⟩ => exact MME.L2Cert.cert_421
  | ⟨54, _⟩ => exact MME.L2Cert.cert_422
  | ⟨55, _⟩ => exact MME.L2Cert.cert_423
  | ⟨56, _⟩ => exact MME.L2Cert.cert_424
  | ⟨57, _⟩ => exact MME.L2Cert.cert_425
  | ⟨58, _⟩ => exact MME.L2Cert.cert_426
  | ⟨59, _⟩ => exact MME.L2Cert.cert_427
  | ⟨60, _⟩ => exact MME.L2Cert.cert_428
  | ⟨61, _⟩ => exact MME.L2Cert.cert_429
  | ⟨62, _⟩ => exact MME.L2Cert.cert_430
  | ⟨63, _⟩ => exact MME.L2Cert.cert_431
  | ⟨64, _⟩ => exact MME.L2Cert.cert_432
  | ⟨65, _⟩ => exact MME.L2Cert.cert_433
  | ⟨66, _⟩ => exact MME.L2Cert.cert_434
  | ⟨67, _⟩ => exact MME.L2Cert.cert_435
  | ⟨68, _⟩ => exact MME.L2Cert.cert_436
  | ⟨69, _⟩ => exact MME.L2Cert.cert_437
  | ⟨70, _⟩ => exact MME.L2Cert.cert_438
  | ⟨71, _⟩ => exact MME.L2Cert.cert_439
  | ⟨72, _⟩ => exact MME.L2Cert.cert_440
  | ⟨73, _⟩ => exact MME.L2Cert.cert_441
  | ⟨74, _⟩ => exact MME.L2Cert.cert_442
  | ⟨75, _⟩ => exact MME.L2Cert.cert_443
  | ⟨76, _⟩ => exact MME.L2Cert.cert_444
  | ⟨77, _⟩ => exact MME.L2Cert.cert_445
  | ⟨78, _⟩ => exact MME.L2Cert.cert_446
  | ⟨79, _⟩ => exact MME.L2Cert.cert_447
  | ⟨80, _⟩ => exact MME.L2Cert.cert_448
  | ⟨81, _⟩ => exact MME.L2Cert.cert_449
  | ⟨82, _⟩ => exact MME.L2Cert.cert_450
  | ⟨83, _⟩ => exact MME.L2Cert.cert_451
  | ⟨84, _⟩ => exact MME.L2Cert.cert_452
  | ⟨85, _⟩ => exact MME.L2Cert.cert_453
  | ⟨86, _⟩ => exact MME.L2Cert.cert_454
  | ⟨87, _⟩ => exact MME.L2Cert.cert_455
  | ⟨88, _⟩ => exact MME.L2Cert.cert_456
  | ⟨89, _⟩ => exact MME.L2Cert.cert_457
  | ⟨90, _⟩ => exact MME.L2Cert.cert_458
  | ⟨91, _⟩ => exact MME.L2Cert.cert_459
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
