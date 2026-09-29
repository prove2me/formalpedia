-- Prove2me | solution 1 for mme_released_recursive_level2_cert3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:12:08.299885+00:00
-- url     : https://prove2.me/submissions/52fce551-507a-4883-bd07-8121dc695baa

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

theorem cert_276 :
    ((certNum ⟨276, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨276, by omega⟩) ⟨276, by omega⟩ (certE ⟨276, by omega⟩) := by
  have hm : certMode (⟨276, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨276, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨276, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨276, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨276, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_277 :
    ((certNum ⟨277, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨277, by omega⟩) ⟨277, by omega⟩ (certE ⟨277, by omega⟩) := by
  have hm : certMode (⟨277, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨277, by omega⟩ : Fin 1104) = 203948413729011842840289552103 := by decide +kernel
  have he : certE (⟨277, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨277, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨277, by omega⟩ : Fin 1104)).2.2 = 21076897359 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_278 :
    ((certNum ⟨278, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨278, by omega⟩) ⟨278, by omega⟩ (certE ⟨278, by omega⟩) := by
  have hm : certMode (⟨278, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨278, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨278, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨278, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨278, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_279 :
    ((certNum ⟨279, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨279, by omega⟩) ⟨279, by omega⟩ (certE ⟨279, by omega⟩) := by
  have hm : certMode (⟨279, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨279, by omega⟩ : Fin 1104) = 203946845678494286637447224698 := by decide +kernel
  have he : certE (⟨279, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨279, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨279, by omega⟩ : Fin 1104)).2.2 = 21076691923 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_280 :
    ((certNum ⟨280, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨280, by omega⟩) ⟨280, by omega⟩ (certE ⟨280, by omega⟩) := by
  have hm : certMode (⟨280, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨280, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨280, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨280, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨280, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_281 :
    ((certNum ⟨281, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨281, by omega⟩) ⟨281, by omega⟩ (certE ⟨281, by omega⟩) := by
  have hm : certMode (⟨281, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨281, by omega⟩ : Fin 1104) = 203946438047800395964947598603 := by decide +kernel
  have he : certE (⟨281, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨281, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨281, by omega⟩ : Fin 1104)).2.2 = 21076638518 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_282 :
    ((certNum ⟨282, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨282, by omega⟩) ⟨282, by omega⟩ (certE ⟨282, by omega⟩) := by
  have hm : certMode (⟨282, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨282, by omega⟩ : Fin 1104) = 10401389901799375079151024798 := by decide +kernel
  have he : certE (⟨282, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -12 else if j.val = 1 then -3 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hp : parent2 (⟨282, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨282, by omega⟩ : Fin 1104)).2.2 = 620256046 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_283 :
    ((certNum ⟨283, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨283, by omega⟩) ⟨283, by omega⟩ (certE ⟨283, by omega⟩) := by
  have hm : certMode (⟨283, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨283, by omega⟩ : Fin 1104) = 203945807858260579408946409048 := by decide +kernel
  have he : certE (⟨283, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨283, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨283, by omega⟩ : Fin 1104)).2.2 = 21076555955 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_284 :
    ((certNum ⟨284, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨284, by omega⟩) ⟨284, by omega⟩ (certE ⟨284, by omega⟩) := by
  have hm : certMode (⟨284, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨284, by omega⟩ : Fin 1104) = 18365524608632542665180330495 := by decide +kernel
  have he : certE (⟨284, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -19 else if j.val = 1 then 8 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hp : parent2 (⟨284, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨284, by omega⟩ : Fin 1104)).2.2 = 1187171261 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_285 :
    ((certNum ⟨285, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨285, by omega⟩) ⟨285, by omega⟩ (certE ⟨285, by omega⟩) := by
  have hm : certMode (⟨285, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨285, by omega⟩ : Fin 1104) = 203945857792299281654232619482 := by decide +kernel
  have he : certE (⟨285, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨285, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨285, by omega⟩ : Fin 1104)).2.2 = 21076562497 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_286 :
    ((certNum ⟨286, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨286, by omega⟩) ⟨286, by omega⟩ (certE ⟨286, by omega⟩) := by
  have hm : certMode (⟨286, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨286, by omega⟩ : Fin 1104) = 10401746605277363536814795967 := by decide +kernel
  have he : certE (⟨286, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -12 else if j.val = 1 then -3 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hp : parent2 (⟨286, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨286, by omega⟩ : Fin 1104)).2.2 = 620280199 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_287 :
    ((certNum ⟨287, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨287, by omega⟩) ⟨287, by omega⟩ (certE ⟨287, by omega⟩) := by
  have hm : certMode (⟨287, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨287, by omega⟩ : Fin 1104) = 203945843923430012665936549477 := by decide +kernel
  have he : certE (⟨287, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨287, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨287, by omega⟩ : Fin 1104)).2.2 = 21076560680 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_288 :
    ((certNum ⟨288, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨288, by omega⟩) ⟨288, by omega⟩ (certE ⟨288, by omega⟩) := by
  have hm : certMode (⟨288, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨288, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨288, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨288, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨288, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_289 :
    ((certNum ⟨289, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨289, by omega⟩) ⟨289, by omega⟩ (certE ⟨289, by omega⟩) := by
  have hm : certMode (⟨289, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨289, by omega⟩ : Fin 1104) = 190579098693795422258110232534 := by decide +kernel
  have he : certE (⟨289, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -5 else -3)) := by decide +kernel
  have hp : parent2 (⟨289, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨289, by omega⟩ : Fin 1104)).2.2 = 19345373774 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_290 :
    ((certNum ⟨290, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨290, by omega⟩) ⟨290, by omega⟩ (certE ⟨290, by omega⟩) := by
  have hm : certMode (⟨290, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨290, by omega⟩ : Fin 1104) = 203945845999562382953180234916 := by decide +kernel
  have he : certE (⟨290, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨290, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨290, by omega⟩ : Fin 1104)).2.2 = 21076560952 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_291 :
    ((certNum ⟨291, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨291, by omega⟩) ⟨291, by omega⟩ (certE ⟨291, by omega⟩) := by
  have hm : certMode (⟨291, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨291, by omega⟩ : Fin 1104) = 89936273361304044648646999519 := by decide +kernel
  have he : certE (⟨291, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -29 else if j.val = 1 then 0 else if j.val = 2 then 1 else 7)) := by decide +kernel
  have hp : parent2 (⟨291, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨291, by omega⟩ : Fin 1104)).2.2 = 7670207021 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_292 :
    ((certNum ⟨292, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨292, by omega⟩) ⟨292, by omega⟩ (certE ⟨292, by omega⟩) := by
  have hm : certMode (⟨292, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨292, by omega⟩ : Fin 1104) = 181068294235139261788546271176 := by decide +kernel
  have he : certE (⟨292, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨292, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨292, by omega⟩ : Fin 1104)).2.2 = 18138103585 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_293 :
    ((certNum ⟨293, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨293, by omega⟩) ⟨293, by omega⟩ (certE ⟨293, by omega⟩) := by
  have hm : certMode (⟨293, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨293, by omega⟩ : Fin 1104) = 203945843106716171807433088381 := by decide +kernel
  have he : certE (⟨293, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨293, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨293, by omega⟩ : Fin 1104)).2.2 = 21076560573 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_294 :
    ((certNum ⟨294, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨294, by omega⟩) ⟨294, by omega⟩ (certE ⟨294, by omega⟩) := by
  have hm : certMode (⟨294, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨294, by omega⟩ : Fin 1104) = 203305766616856103663573986691 := by decide +kernel
  have he : certE (⟨294, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨294, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨294, by omega⟩ : Fin 1104)).2.2 = 20992750304 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_295 :
    ((certNum ⟨295, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨295, by omega⟩) ⟨295, by omega⟩ (certE ⟨295, by omega⟩) := by
  have hm : certMode (⟨295, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨295, by omega⟩ : Fin 1104) = 180781992120060764806136890137 := by decide +kernel
  have he : certE (⟨295, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hp : parent2 (⟨295, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨295, by omega⟩ : Fin 1104)).2.2 = 18102080563 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_296 :
    ((certNum ⟨296, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨296, by omega⟩) ⟨296, by omega⟩ (certE ⟨296, by omega⟩) := by
  have hm : certMode (⟨296, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨296, by omega⟩ : Fin 1104) = 91298541655905249624811155701 := by decide +kernel
  have he : certE (⟨296, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -6 else if j.val = 1 then 7 else if j.val = 2 then -4 else -1)) := by decide +kernel
  have hp : parent2 (⟨296, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨296, by omega⟩ : Fin 1104)).2.2 = 7810771429 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_297 :
    ((certNum ⟨297, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨297, by omega⟩) ⟨297, by omega⟩ (certE ⟨297, by omega⟩) := by
  have hm : certMode (⟨297, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨297, by omega⟩ : Fin 1104) = 203305772584790694088456531551 := by decide +kernel
  have he : certE (⟨297, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨297, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨297, by omega⟩ : Fin 1104)).2.2 = 20992751085 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_298 :
    ((certNum ⟨298, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨298, by omega⟩) ⟨298, by omega⟩ (certE ⟨298, by omega⟩) := by
  have hm : certMode (⟨298, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨298, by omega⟩ : Fin 1104) = 190496383423829469704046079030 := by decide +kernel
  have he : certE (⟨298, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 13 else if j.val = 1 then 5 else if j.val = 2 then -3 else -7)) := by decide +kernel
  have hp : parent2 (⟨298, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨298, by omega⟩ : Fin 1104)).2.2 = 19334785981 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_299 :
    ((certNum ⟨299, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨299, by omega⟩) ⟨299, by omega⟩ (certE ⟨299, by omega⟩) := by
  have hm : certMode (⟨299, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨299, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨299, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨299, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨299, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_300 :
    ((certNum ⟨300, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨300, by omega⟩) ⟨300, by omega⟩ (certE ⟨300, by omega⟩) := by
  have hm : certMode (⟨300, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨300, by omega⟩ : Fin 1104) = 181445988739769102287346362631 := by decide +kernel
  have he : certE (⟨300, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hp : parent2 (⟨300, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨300, by omega⟩ : Fin 1104)).2.2 = 18185655046 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_301 :
    ((certNum ⟨301, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨301, by omega⟩) ⟨301, by omega⟩ (certE ⟨301, by omega⟩) := by
  have hm : certMode (⟨301, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨301, by omega⟩ : Fin 1104) = 89085498532486693518386561511 := by decide +kernel
  have he : certE (⟨301, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 12 else if j.val = 1 then -2 else if j.val = 2 then -2 else -4)) := by decide +kernel
  have hp : parent2 (⟨301, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨301, by omega⟩ : Fin 1104)).2.2 = 7582692521 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_302 :
    ((certNum ⟨302, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨302, by omega⟩) ⟨302, by omega⟩ (certE ⟨302, by omega⟩) := by
  have hm : certMode (⟨302, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨302, by omega⟩ : Fin 1104) = 203945840045947458315342031249 := by decide +kernel
  have he : certE (⟨302, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨302, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨302, by omega⟩ : Fin 1104)).2.2 = 21076560172 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_303 :
    ((certNum ⟨303, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨303, by omega⟩) ⟨303, by omega⟩ (certE ⟨303, by omega⟩) := by
  have hm : certMode (⟨303, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨303, by omega⟩ : Fin 1104) = 190769423979174330537265251598 := by decide +kernel
  have he : certE (⟨303, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨303, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨303, by omega⟩ : Fin 1104)).2.2 = 19369742058 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_304 :
    ((certNum ⟨304, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨304, by omega⟩) ⟨304, by omega⟩ (certE ⟨304, by omega⟩) := by
  have hm : certMode (⟨304, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨304, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨304, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨304, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨304, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_305 :
    ((certNum ⟨305, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨305, by omega⟩) ⟨305, by omega⟩ (certE ⟨305, by omega⟩) := by
  have hm : certMode (⟨305, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨305, by omega⟩ : Fin 1104) = 203945841961790222859560451902 := by decide +kernel
  have he : certE (⟨305, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨305, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨305, by omega⟩ : Fin 1104)).2.2 = 21076560423 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_306 :
    ((certNum ⟨306, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨306, by omega⟩) ⟨306, by omega⟩ (certE ⟨306, by omega⟩) := by
  have hm : certMode (⟨306, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨306, by omega⟩ : Fin 1104) = 180945787517126821476918925011 := by decide +kernel
  have he : certE (⟨306, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 14 else if j.val = 1 then -4 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨306, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨306, by omega⟩ : Fin 1104)).2.2 = 18122687219 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_307 :
    ((certNum ⟨307, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨307, by omega⟩) ⟨307, by omega⟩ (certE ⟨307, by omega⟩) := by
  have hm : certMode (⟨307, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨307, by omega⟩ : Fin 1104) = 202779598879243441082946825686 := by decide +kernel
  have he : certE (⟨307, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨307, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨307, by omega⟩ : Fin 1104)).2.2 = 20923923010 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_308 :
    ((certNum ⟨308, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨308, by omega⟩) ⟨308, by omega⟩ (certE ⟨308, by omega⟩) := by
  have hm : certMode (⟨308, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨308, by omega⟩ : Fin 1104) = 91607981225932885324435311600 := by decide +kernel
  have he : certE (⟨308, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -6 else if j.val = 1 then -1 else if j.val = 2 then -7 else 6)) := by decide +kernel
  have hp : parent2 (⟨308, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨308, by omega⟩ : Fin 1104)).2.2 = 7842775364 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_309 :
    ((certNum ⟨309, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨309, by omega⟩) ⟨309, by omega⟩ (certE ⟨309, by omega⟩) := by
  have hm : certMode (⟨309, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨309, by omega⟩ : Fin 1104) = 190641473752121299045781850420 := by decide +kernel
  have he : certE (⟨309, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨309, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨309, by omega⟩ : Fin 1104)).2.2 = 19353359058 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_310 :
    ((certNum ⟨310, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨310, by omega⟩) ⟨310, by omega⟩ (certE ⟨310, by omega⟩) := by
  have hm : certMode (⟨310, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨310, by omega⟩ : Fin 1104) = 202779584286569410271337471638 := by decide +kernel
  have he : certE (⟨310, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨310, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨310, by omega⟩ : Fin 1104)).2.2 = 20923921102 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_311 :
    ((certNum ⟨311, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨311, by omega⟩) ⟨311, by omega⟩ (certE ⟨311, by omega⟩) := by
  have hm : certMode (⟨311, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨311, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨311, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨311, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨311, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_312 :
    ((certNum ⟨312, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨312, by omega⟩) ⟨312, by omega⟩ (certE ⟨312, by omega⟩) := by
  have hm : certMode (⟨312, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨312, by omega⟩ : Fin 1104) = 10484991908147841351076926316 := by decide +kernel
  have he : certE (⟨312, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -26 else if j.val = 1 then 7 else if j.val = 2 then -3 else 4)) := by decide +kernel
  have hp : parent2 (⟨312, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨312, by omega⟩ : Fin 1104)).2.2 = 625920403 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_313 :
    ((certNum ⟨313, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨313, by omega⟩) ⟨313, by omega⟩ (certE ⟨313, by omega⟩) := by
  have hm : certMode (⟨313, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨313, by omega⟩ : Fin 1104) = 203945858983022204360602430123 := by decide +kernel
  have he : certE (⟨313, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨313, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨313, by omega⟩ : Fin 1104)).2.2 = 21076562653 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_314 :
    ((certNum ⟨314, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨314, by omega⟩) ⟨314, by omega⟩ (certE ⟨314, by omega⟩) := by
  have hm : certMode (⟨314, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨314, by omega⟩ : Fin 1104) = 5014648086817119780034724119 := by decide +kernel
  have he : certE (⟨314, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -10 else if j.val = 1 then 8 else if j.val = 2 then 1 else -6)) := by decide +kernel
  have hp : parent2 (⟨314, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨314, by omega⟩ : Fin 1104)).2.2 = 272287286 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_315 :
    ((certNum ⟨315, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨315, by omega⟩) ⟨315, by omega⟩ (certE ⟨315, by omega⟩) := by
  have hm : certMode (⟨315, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨315, by omega⟩ : Fin 1104) = 203945632066257097563650179289 := by decide +kernel
  have he : certE (⟨315, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨315, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨315, by omega⟩ : Fin 1104)).2.2 = 21076532924 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_316 :
    ((certNum ⟨316, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨316, by omega⟩) ⟨316, by omega⟩ (certE ⟨316, by omega⟩) := by
  have hm : certMode (⟨316, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨316, by omega⟩ : Fin 1104) = 5015664769422948132297734959 := by decide +kernel
  have he : certE (⟨316, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -10 else if j.val = 1 then -3 else if j.val = 2 then -6 else 6)) := by decide +kernel
  have hp : parent2 (⟨316, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨316, by omega⟩ : Fin 1104)).2.2 = 272349218 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_317 :
    ((certNum ⟨317, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨317, by omega⟩) ⟨317, by omega⟩ (certE ⟨317, by omega⟩) := by
  have hm : certMode (⟨317, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨317, by omega⟩ : Fin 1104) = 203945831840644640263906341368 := by decide +kernel
  have he : certE (⟨317, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨317, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨317, by omega⟩ : Fin 1104)).2.2 = 21076559097 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_318 :
    ((certNum ⟨318, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨318, by omega⟩) ⟨318, by omega⟩ (certE ⟨318, by omega⟩) := by
  have hm : certMode (⟨318, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨318, by omega⟩ : Fin 1104) = 203305770697364530720960285602 := by decide +kernel
  have he : certE (⟨318, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨318, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨318, by omega⟩ : Fin 1104)).2.2 = 20992750838 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_319 :
    ((certNum ⟨319, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨319, by omega⟩) ⟨319, by omega⟩ (certE ⟨319, by omega⟩) := by
  have hm : certMode (⟨319, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨319, by omega⟩ : Fin 1104) = 15739010374203263326810230003 := by decide +kernel
  have he : certE (⟨319, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -35 else if j.val = 1 then 7 else if j.val = 2 then 6 else 0)) := by decide +kernel
  have hp : parent2 (⟨319, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨319, by omega⟩ : Fin 1104)).2.2 = 994608148 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_320 :
    ((certNum ⟨320, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨320, by omega⟩) ⟨320, by omega⟩ (certE ⟨320, by omega⟩) := by
  have hm : certMode (⟨320, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨320, by omega⟩ : Fin 1104) = 203305786155919349482638652512 := by decide +kernel
  have he : certE (⟨320, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨320, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨320, by omega⟩ : Fin 1104)).2.2 = 20992752861 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_321 :
    ((certNum ⟨321, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨321, by omega⟩) ⟨321, by omega⟩ (certE ⟨321, by omega⟩) := by
  have hm : certMode (⟨321, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨321, by omega⟩ : Fin 1104) = 25356793425882515632266602647 := by decide +kernel
  have he : certE (⟨321, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -6 else if j.val = 1 then 3 else if j.val = 2 then -1 else -2)) := by decide +kernel
  have hp : parent2 (⟨321, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨321, by omega⟩ : Fin 1104)).2.2 = 1722015002 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_322 :
    ((certNum ⟨322, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨322, by omega⟩) ⟨322, by omega⟩ (certE ⟨322, by omega⟩) := by
  have hm : certMode (⟨322, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨322, by omega⟩ : Fin 1104) = 203305742256066786011733455566 := by decide +kernel
  have he : certE (⟨322, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨322, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨322, by omega⟩ : Fin 1104)).2.2 = 20992747116 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_323 :
    ((certNum ⟨323, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨323, by omega⟩) ⟨323, by omega⟩ (certE ⟨323, by omega⟩) := by
  have hm : certMode (⟨323, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨323, by omega⟩ : Fin 1104) = 15739747395079769384026981230 := by decide +kernel
  have he : certE (⟨323, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 12 else if j.val = 1 then 0 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨323, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨323, by omega⟩ : Fin 1104)).2.2 = 994661469 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_324 :
    ((certNum ⟨324, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨324, by omega⟩) ⟨324, by omega⟩ (certE ⟨324, by omega⟩) := by
  have hm : certMode (⟨324, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨324, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨324, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨324, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨324, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_325 :
    ((certNum ⟨325, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨325, by omega⟩) ⟨325, by omega⟩ (certE ⟨325, by omega⟩) := by
  have hm : certMode (⟨325, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨325, by omega⟩ : Fin 1104) = 3055261681196594992256178 := by decide +kernel
  have he : certE (⟨325, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -15 else if j.val = 1 then -3 else if j.val = 2 then -4 else 2)) := by decide +kernel
  have hp : parent2 (⟨325, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨325, by omega⟩ : Fin 1104)).2.2 = 88615 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_326 :
    ((certNum ⟨326, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨326, by omega⟩) ⟨326, by omega⟩ (certE ⟨326, by omega⟩) := by
  have hm : certMode (⟨326, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨326, by omega⟩ : Fin 1104) = 203945823108675622399521493668 := by decide +kernel
  have he : certE (⟨326, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨326, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨326, by omega⟩ : Fin 1104)).2.2 = 21076557953 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_327 :
    ((certNum ⟨327, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨327, by omega⟩) ⟨327, by omega⟩ (certE ⟨327, by omega⟩) := by
  have hm : certMode (⟨327, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨327, by omega⟩ : Fin 1104) = 3074257414409062467996914 := by decide +kernel
  have he : certE (⟨327, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -42 else if j.val = 1 then -8 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨327, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨327, by omega⟩ : Fin 1104)).2.2 = 89200 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_328 :
    ((certNum ⟨328, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨328, by omega⟩) ⟨328, by omega⟩ (certE ⟨328, by omega⟩) := by
  have hm : certMode (⟨328, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨328, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨328, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨328, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨328, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_329 :
    ((certNum ⟨329, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨329, by omega⟩) ⟨329, by omega⟩ (certE ⟨329, by omega⟩) := by
  have hm : certMode (⟨329, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨329, by omega⟩ : Fin 1104) = 203945822833893376370141651819 := by decide +kernel
  have he : certE (⟨329, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨329, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨329, by omega⟩ : Fin 1104)).2.2 = 21076557917 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_330 :
    ((certNum ⟨330, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨330, by omega⟩) ⟨330, by omega⟩ (certE ⟨330, by omega⟩) := by
  have hm : certMode (⟨330, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨330, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨330, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨330, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨330, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_331 :
    ((certNum ⟨331, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨331, by omega⟩) ⟨331, by omega⟩ (certE ⟨331, by omega⟩) := by
  have hm : certMode (⟨331, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨331, by omega⟩ : Fin 1104) = 203774664705547577824209202114 := by decide +kernel
  have he : certE (⟨331, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨331, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨331, by omega⟩ : Fin 1104)).2.2 = 21054137529 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_332 :
    ((certNum ⟨332, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨332, by omega⟩) ⟨332, by omega⟩ (certE ⟨332, by omega⟩) := by
  have hm : certMode (⟨332, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨332, by omega⟩ : Fin 1104) = 177447246295334551961113824148 := by decide +kernel
  have he : certE (⟨332, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 17 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨332, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨332, by omega⟩ : Fin 1104)).2.2 = 17683870266 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_333 :
    ((certNum ⟨333, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨333, by omega⟩) ⟨333, by omega⟩ (certE ⟨333, by omega⟩) := by
  have hm : certMode (⟨333, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨333, by omega⟩ : Fin 1104) = 203880670704022499015396213022 := by decide +kernel
  have he : certE (⟨333, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨333, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨333, by omega⟩ : Fin 1104)).2.2 = 21068022707 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_334 :
    ((certNum ⟨334, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨334, by omega⟩) ⟨334, by omega⟩ (certE ⟨334, by omega⟩) := by
  have hm : certMode (⟨334, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨334, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨334, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨334, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨334, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_335 :
    ((certNum ⟨335, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨335, by omega⟩) ⟨335, by omega⟩ (certE ⟨335, by omega⟩) := by
  have hm : certMode (⟨335, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨335, by omega⟩ : Fin 1104) = 177418409121034773755629675266 := by decide +kernel
  have he : certE (⟨335, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 18 else if j.val = 1 then 5 else if j.val = 2 then -4 else -8)) := by decide +kernel
  have hp : parent2 (⟨335, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨335, by omega⟩ : Fin 1104)).2.2 = 17680264850 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_336 :
    ((certNum ⟨336, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨336, by omega⟩) ⟨336, by omega⟩ (certE ⟨336, by omega⟩) := by
  have hm : certMode (⟨336, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨336, by omega⟩ : Fin 1104) = 202779576301898406698773188985 := by decide +kernel
  have he : certE (⟨336, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨336, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨336, by omega⟩ : Fin 1104)).2.2 = 20923920058 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_337 :
    ((certNum ⟨337, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨337, by omega⟩) ⟨337, by omega⟩ (certE ⟨337, by omega⟩) := by
  have hm : certMode (⟨337, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨337, by omega⟩ : Fin 1104) = 25544210780833332119567154569 := by decide +kernel
  have he : certE (⟨337, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -11 else if j.val = 1 then -3 else if j.val = 2 then -2 else 4)) := by decide +kernel
  have hp : parent2 (⟨337, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨337, by omega⟩ : Fin 1104)).2.2 = 1736757007 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_338 :
    ((certNum ⟨338, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨338, by omega⟩) ⟨338, by omega⟩ (certE ⟨338, by omega⟩) := by
  have hm : certMode (⟨338, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨338, by omega⟩ : Fin 1104) = 202779785348773597026267691049 := by decide +kernel
  have he : certE (⟨338, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨338, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨338, by omega⟩ : Fin 1104)).2.2 = 20923947391 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_339 :
    ((certNum ⟨339, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨339, by omega⟩) ⟨339, by omega⟩ (certE ⟨339, by omega⟩) := by
  have hm : certMode (⟨339, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨339, by omega⟩ : Fin 1104) = 15880574124796764746619084845 := by decide +kernel
  have he : certE (⟨339, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then -3 else 3)) := by decide +kernel
  have hp : parent2 (⟨339, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨339, by omega⟩ : Fin 1104)).2.2 = 1004857439 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_340 :
    ((certNum ⟨340, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨340, by omega⟩) ⟨340, by omega⟩ (certE ⟨340, by omega⟩) := by
  have hm : certMode (⟨340, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨340, by omega⟩ : Fin 1104) = 202779655483209577056601223790 := by decide +kernel
  have he : certE (⟨340, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨340, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨340, by omega⟩ : Fin 1104)).2.2 = 20923930411 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_341 :
    ((certNum ⟨341, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨341, by omega⟩) ⟨341, by omega⟩ (certE ⟨341, by omega⟩) := by
  have hm : certMode (⟨341, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨341, by omega⟩ : Fin 1104) = 15881524757598125848631604950 := by decide +kernel
  have he : certE (⟨341, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then -3 else 3)) := by decide +kernel
  have hp : parent2 (⟨341, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨341, by omega⟩ : Fin 1104)).2.2 = 1004926317 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_342 :
    ((certNum ⟨342, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨342, by omega⟩) ⟨342, by omega⟩ (certE ⟨342, by omega⟩) := by
  have hm : certMode (⟨342, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨342, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨342, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨342, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨342, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_343 :
    ((certNum ⟨343, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨343, by omega⟩) ⟨343, by omega⟩ (certE ⟨343, by omega⟩) := by
  have hm : certMode (⟨343, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨343, by omega⟩ : Fin 1104) = 203945806514880637815718176974 := by decide +kernel
  have he : certE (⟨343, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨343, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨343, by omega⟩ : Fin 1104)).2.2 = 21076555779 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_344 :
    ((certNum ⟨344, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨344, by omega⟩) ⟨344, by omega⟩ (certE ⟨344, by omega⟩) := by
  have hm : certMode (⟨344, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨344, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨344, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨344, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨344, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_345 :
    ((certNum ⟨345, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨345, by omega⟩) ⟨345, by omega⟩ (certE ⟨345, by omega⟩) := by
  have hm : certMode (⟨345, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨345, by omega⟩ : Fin 1104) = 203945815468202519051589711212 := by decide +kernel
  have he : certE (⟨345, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨345, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨345, by omega⟩ : Fin 1104)).2.2 = 21076556952 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_346 :
    ((certNum ⟨346, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨346, by omega⟩) ⟨346, by omega⟩ (certE ⟨346, by omega⟩) := by
  have hm : certMode (⟨346, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨346, by omega⟩ : Fin 1104) = 203877791459170273227226409566 := by decide +kernel
  have he : certE (⟨346, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨346, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨346, by omega⟩ : Fin 1104)).2.2 = 21067645532 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_347 :
    ((certNum ⟨347, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨347, by omega⟩) ⟨347, by omega⟩ (certE ⟨347, by omega⟩) := by
  have hm : certMode (⟨347, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨347, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨347, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨347, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨347, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_348 :
    ((certNum ⟨348, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨348, by omega⟩) ⟨348, by omega⟩ (certE ⟨348, by omega⟩) := by
  have hm : certMode (⟨348, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨348, by omega⟩ : Fin 1104) = 203875139571477600637606847130 := by decide +kernel
  have he : certE (⟨348, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨348, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨348, by omega⟩ : Fin 1104)).2.2 = 21067298138 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_349 :
    ((certNum ⟨349, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨349, by omega⟩) ⟨349, by omega⟩ (certE ⟨349, by omega⟩) := by
  have hm : certMode (⟨349, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨349, by omega⟩ : Fin 1104) = 39756703108517064609439795658 := by decide +kernel
  have he : certE (⟨349, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -12 else if j.val = 1 then -8 else if j.val = 2 then 7 else 0)) := by decide +kernel
  have hp : parent2 (⟨349, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨349, by omega⟩ : Fin 1104)).2.2 = 2907187957 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_350 :
    ((certNum ⟨350, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨350, by omega⟩) ⟨350, by omega⟩ (certE ⟨350, by omega⟩) := by
  have hm : certMode (⟨350, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨350, by omega⟩ : Fin 1104) = 203877255440759314478609624714 := by decide +kernel
  have he : certE (⟨350, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨350, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨350, by omega⟩ : Fin 1104)).2.2 = 21067575314 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_351 :
    ((certNum ⟨351, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨351, by omega⟩) ⟨351, by omega⟩ (certE ⟨351, by omega⟩) := by
  have hm : certMode (⟨351, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨351, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨351, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨351, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨351, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_352 :
    ((certNum ⟨352, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨352, by omega⟩) ⟨352, by omega⟩ (certE ⟨352, by omega⟩) := by
  have hm : certMode (⟨352, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨352, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨352, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨352, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨352, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_353 :
    ((certNum ⟨353, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨353, by omega⟩) ⟨353, by omega⟩ (certE ⟨353, by omega⟩) := by
  have hm : certMode (⟨353, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨353, by omega⟩ : Fin 1104) = 203945802728991678486474248984 := by decide +kernel
  have he : certE (⟨353, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨353, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨353, by omega⟩ : Fin 1104)).2.2 = 21076555283 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_354 :
    ((certNum ⟨354, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨354, by omega⟩) ⟨354, by omega⟩ (certE ⟨354, by omega⟩) := by
  have hm : certMode (⟨354, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨354, by omega⟩ : Fin 1104) = 203771748354827137645671628018 := by decide +kernel
  have he : certE (⟨354, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨354, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨354, by omega⟩ : Fin 1104)).2.2 = 21053755561 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_355 :
    ((certNum ⟨355, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨355, by omega⟩) ⟨355, by omega⟩ (certE ⟨355, by omega⟩) := by
  have hm : certMode (⟨355, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨355, by omega⟩ : Fin 1104) = 39814439979436829770875562876 := by decide +kernel
  have he : certE (⟨355, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -36 else if j.val = 1 then 5 else if j.val = 2 then 0 else 7)) := by decide +kernel
  have hp : parent2 (⟨355, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨355, by omega⟩ : Fin 1104)).2.2 = 2912136387 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_356 :
    ((certNum ⟨356, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨356, by omega⟩) ⟨356, by omega⟩ (certE ⟨356, by omega⟩) := by
  have hm : certMode (⟨356, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨356, by omega⟩ : Fin 1104) = 203772879416874068035947227665 := by decide +kernel
  have he : certE (⟨356, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨356, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨356, by omega⟩ : Fin 1104)).2.2 = 21053903701 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_357 :
    ((certNum ⟨357, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨357, by omega⟩) ⟨357, by omega⟩ (certE ⟨357, by omega⟩) := by
  have hm : certMode (⟨357, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨357, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨357, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨357, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨357, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_358 :
    ((certNum ⟨358, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨358, by omega⟩) ⟨358, by omega⟩ (certE ⟨358, by omega⟩) := by
  have hm : certMode (⟨358, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨358, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨358, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨358, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨358, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_359 :
    ((certNum ⟨359, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨359, by omega⟩) ⟨359, by omega⟩ (certE ⟨359, by omega⟩) := by
  have hm : certMode (⟨359, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨359, by omega⟩ : Fin 1104) = 203945812804341220558380251470 := by decide +kernel
  have he : certE (⟨359, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨359, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨359, by omega⟩ : Fin 1104)).2.2 = 21076556603 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_360 :
    ((certNum ⟨360, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨360, by omega⟩) ⟨360, by omega⟩ (certE ⟨360, by omega⟩) := by
  have hm : certMode (⟨360, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨360, by omega⟩ : Fin 1104) = 203773262216332642870929825039 := by decide +kernel
  have he : certE (⟨360, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨360, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨360, by omega⟩ : Fin 1104)).2.2 = 21053953838 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_361 :
    ((certNum ⟨361, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨361, by omega⟩) ⟨361, by omega⟩ (certE ⟨361, by omega⟩) := by
  have hm : certMode (⟨361, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨361, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨361, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨361, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨361, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_362 :
    ((certNum ⟨362, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨362, by omega⟩) ⟨362, by omega⟩ (certE ⟨362, by omega⟩) := by
  have hm : certMode (⟨362, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨362, by omega⟩ : Fin 1104) = 203948760760460374283104745784 := by decide +kernel
  have he : certE (⟨362, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨362, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨362, by omega⟩ : Fin 1104)).2.2 = 21076942825 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_363 :
    ((certNum ⟨363, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨363, by omega⟩) ⟨363, by omega⟩ (certE ⟨363, by omega⟩) := by
  have hm : certMode (⟨363, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨363, by omega⟩ : Fin 1104) = 203948760684132735215615428734 := by decide +kernel
  have he : certE (⟨363, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨363, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨363, by omega⟩ : Fin 1104)).2.2 = 21076942815 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_364 :
    ((certNum ⟨364, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨364, by omega⟩) ⟨364, by omega⟩ (certE ⟨364, by omega⟩) := by
  have hm : certMode (⟨364, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨364, by omega⟩ : Fin 1104) = 203948759088885074170578330881 := by decide +kernel
  have he : certE (⟨364, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨364, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨364, by omega⟩ : Fin 1104)).2.2 = 21076942606 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_365 :
    ((certNum ⟨365, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨365, by omega⟩) ⟨365, by omega⟩ (certE ⟨365, by omega⟩) := by
  have hm : certMode (⟨365, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨365, by omega⟩ : Fin 1104) = 203948747624473399045053963213 := by decide +kernel
  have he : certE (⟨365, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨365, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨365, by omega⟩ : Fin 1104)).2.2 = 21076941104 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_366 :
    ((certNum ⟨366, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨366, by omega⟩) ⟨366, by omega⟩ (certE ⟨366, by omega⟩) := by
  have hm : certMode (⟨366, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨366, by omega⟩ : Fin 1104) = 203948759035455726521669162353 := by decide +kernel
  have he : certE (⟨366, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨366, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨366, by omega⟩ : Fin 1104)).2.2 = 21076942599 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_367 :
    ((certNum ⟨367, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨367, by omega⟩) ⟨367, by omega⟩ (certE ⟨367, by omega⟩) := by
  have hm : certMode (⟨367, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨367, by omega⟩ : Fin 1104) = 203948747876354619080098019299 := by decide +kernel
  have he : certE (⟨367, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨367, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨367, by omega⟩ : Fin 1104)).2.2 = 21076941137 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨276 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨276 + j.val, by omega⟩) ⟨276 + j.val, by omega⟩
        (certE ⟨276 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_276
  | ⟨1, _⟩ => exact MME.L2Cert.cert_277
  | ⟨2, _⟩ => exact MME.L2Cert.cert_278
  | ⟨3, _⟩ => exact MME.L2Cert.cert_279
  | ⟨4, _⟩ => exact MME.L2Cert.cert_280
  | ⟨5, _⟩ => exact MME.L2Cert.cert_281
  | ⟨6, _⟩ => exact MME.L2Cert.cert_282
  | ⟨7, _⟩ => exact MME.L2Cert.cert_283
  | ⟨8, _⟩ => exact MME.L2Cert.cert_284
  | ⟨9, _⟩ => exact MME.L2Cert.cert_285
  | ⟨10, _⟩ => exact MME.L2Cert.cert_286
  | ⟨11, _⟩ => exact MME.L2Cert.cert_287
  | ⟨12, _⟩ => exact MME.L2Cert.cert_288
  | ⟨13, _⟩ => exact MME.L2Cert.cert_289
  | ⟨14, _⟩ => exact MME.L2Cert.cert_290
  | ⟨15, _⟩ => exact MME.L2Cert.cert_291
  | ⟨16, _⟩ => exact MME.L2Cert.cert_292
  | ⟨17, _⟩ => exact MME.L2Cert.cert_293
  | ⟨18, _⟩ => exact MME.L2Cert.cert_294
  | ⟨19, _⟩ => exact MME.L2Cert.cert_295
  | ⟨20, _⟩ => exact MME.L2Cert.cert_296
  | ⟨21, _⟩ => exact MME.L2Cert.cert_297
  | ⟨22, _⟩ => exact MME.L2Cert.cert_298
  | ⟨23, _⟩ => exact MME.L2Cert.cert_299
  | ⟨24, _⟩ => exact MME.L2Cert.cert_300
  | ⟨25, _⟩ => exact MME.L2Cert.cert_301
  | ⟨26, _⟩ => exact MME.L2Cert.cert_302
  | ⟨27, _⟩ => exact MME.L2Cert.cert_303
  | ⟨28, _⟩ => exact MME.L2Cert.cert_304
  | ⟨29, _⟩ => exact MME.L2Cert.cert_305
  | ⟨30, _⟩ => exact MME.L2Cert.cert_306
  | ⟨31, _⟩ => exact MME.L2Cert.cert_307
  | ⟨32, _⟩ => exact MME.L2Cert.cert_308
  | ⟨33, _⟩ => exact MME.L2Cert.cert_309
  | ⟨34, _⟩ => exact MME.L2Cert.cert_310
  | ⟨35, _⟩ => exact MME.L2Cert.cert_311
  | ⟨36, _⟩ => exact MME.L2Cert.cert_312
  | ⟨37, _⟩ => exact MME.L2Cert.cert_313
  | ⟨38, _⟩ => exact MME.L2Cert.cert_314
  | ⟨39, _⟩ => exact MME.L2Cert.cert_315
  | ⟨40, _⟩ => exact MME.L2Cert.cert_316
  | ⟨41, _⟩ => exact MME.L2Cert.cert_317
  | ⟨42, _⟩ => exact MME.L2Cert.cert_318
  | ⟨43, _⟩ => exact MME.L2Cert.cert_319
  | ⟨44, _⟩ => exact MME.L2Cert.cert_320
  | ⟨45, _⟩ => exact MME.L2Cert.cert_321
  | ⟨46, _⟩ => exact MME.L2Cert.cert_322
  | ⟨47, _⟩ => exact MME.L2Cert.cert_323
  | ⟨48, _⟩ => exact MME.L2Cert.cert_324
  | ⟨49, _⟩ => exact MME.L2Cert.cert_325
  | ⟨50, _⟩ => exact MME.L2Cert.cert_326
  | ⟨51, _⟩ => exact MME.L2Cert.cert_327
  | ⟨52, _⟩ => exact MME.L2Cert.cert_328
  | ⟨53, _⟩ => exact MME.L2Cert.cert_329
  | ⟨54, _⟩ => exact MME.L2Cert.cert_330
  | ⟨55, _⟩ => exact MME.L2Cert.cert_331
  | ⟨56, _⟩ => exact MME.L2Cert.cert_332
  | ⟨57, _⟩ => exact MME.L2Cert.cert_333
  | ⟨58, _⟩ => exact MME.L2Cert.cert_334
  | ⟨59, _⟩ => exact MME.L2Cert.cert_335
  | ⟨60, _⟩ => exact MME.L2Cert.cert_336
  | ⟨61, _⟩ => exact MME.L2Cert.cert_337
  | ⟨62, _⟩ => exact MME.L2Cert.cert_338
  | ⟨63, _⟩ => exact MME.L2Cert.cert_339
  | ⟨64, _⟩ => exact MME.L2Cert.cert_340
  | ⟨65, _⟩ => exact MME.L2Cert.cert_341
  | ⟨66, _⟩ => exact MME.L2Cert.cert_342
  | ⟨67, _⟩ => exact MME.L2Cert.cert_343
  | ⟨68, _⟩ => exact MME.L2Cert.cert_344
  | ⟨69, _⟩ => exact MME.L2Cert.cert_345
  | ⟨70, _⟩ => exact MME.L2Cert.cert_346
  | ⟨71, _⟩ => exact MME.L2Cert.cert_347
  | ⟨72, _⟩ => exact MME.L2Cert.cert_348
  | ⟨73, _⟩ => exact MME.L2Cert.cert_349
  | ⟨74, _⟩ => exact MME.L2Cert.cert_350
  | ⟨75, _⟩ => exact MME.L2Cert.cert_351
  | ⟨76, _⟩ => exact MME.L2Cert.cert_352
  | ⟨77, _⟩ => exact MME.L2Cert.cert_353
  | ⟨78, _⟩ => exact MME.L2Cert.cert_354
  | ⟨79, _⟩ => exact MME.L2Cert.cert_355
  | ⟨80, _⟩ => exact MME.L2Cert.cert_356
  | ⟨81, _⟩ => exact MME.L2Cert.cert_357
  | ⟨82, _⟩ => exact MME.L2Cert.cert_358
  | ⟨83, _⟩ => exact MME.L2Cert.cert_359
  | ⟨84, _⟩ => exact MME.L2Cert.cert_360
  | ⟨85, _⟩ => exact MME.L2Cert.cert_361
  | ⟨86, _⟩ => exact MME.L2Cert.cert_362
  | ⟨87, _⟩ => exact MME.L2Cert.cert_363
  | ⟨88, _⟩ => exact MME.L2Cert.cert_364
  | ⟨89, _⟩ => exact MME.L2Cert.cert_365
  | ⟨90, _⟩ => exact MME.L2Cert.cert_366
  | ⟨91, _⟩ => exact MME.L2Cert.cert_367
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
