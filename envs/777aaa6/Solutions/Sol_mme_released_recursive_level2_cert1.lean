-- Prove2me | solution 1 for mme_released_recursive_level2_cert1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T23:58:09.206851+00:00
-- url     : https://prove2.me/submissions/752f48f7-b97a-4f34-80ef-51e44d2381d3

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

theorem cert_92 :
    ((certNum ⟨92, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨92, by omega⟩) ⟨92, by omega⟩ (certE ⟨92, by omega⟩) := by
  have hm : certMode (⟨92, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨92, by omega⟩ : Fin 1104) = 180755635493521625340483863132 := by decide +kernel
  have he : certE (⟨92, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -18 else if j.val = 1 then -5 else if j.val = 2 then -1 else 8)) := by decide +kernel
  have hp : parent2 (⟨92, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨92, by omega⟩ : Fin 1104)).2.2 = 18098765117 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_93 :
    ((certNum ⟨93, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨93, by omega⟩) ⟨93, by omega⟩ (certE ⟨93, by omega⟩) := by
  have hm : certMode (⟨93, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨93, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨93, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨93, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨93, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_94 :
    ((certNum ⟨94, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨94, by omega⟩) ⟨94, by omega⟩ (certE ⟨94, by omega⟩) := by
  have hm : certMode (⟨94, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨94, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨94, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨94, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨94, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_95 :
    ((certNum ⟨95, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨95, by omega⟩) ⟨95, by omega⟩ (certE ⟨95, by omega⟩) := by
  have hm : certMode (⟨95, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨95, by omega⟩ : Fin 1104) = 203946666391280524551231359209 := by decide +kernel
  have he : certE (⟨95, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨95, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨95, by omega⟩ : Fin 1104)).2.2 = 21076668434 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_96 :
    ((certNum ⟨96, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨96, by omega⟩) ⟨96, by omega⟩ (certE ⟨96, by omega⟩) := by
  have hm : certMode (⟨96, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨96, by omega⟩ : Fin 1104) = 180751337031072305312020970751 := by decide +kernel
  have he : certE (⟨96, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -18 else if j.val = 1 then 6 else if j.val = 2 then 6 else -4)) := by decide +kernel
  have hp : parent2 (⟨96, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨96, by omega⟩ : Fin 1104)).2.2 = 18098224427 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_97 :
    ((certNum ⟨97, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨97, by omega⟩) ⟨97, by omega⟩ (certE ⟨97, by omega⟩) := by
  have hm : certMode (⟨97, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨97, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨97, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨97, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨97, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_98 :
    ((certNum ⟨98, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨98, by omega⟩) ⟨98, by omega⟩ (certE ⟨98, by omega⟩) := by
  have hm : certMode (⟨98, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨98, by omega⟩ : Fin 1104) = 5023684003043564157890765345 := by decide +kernel
  have he : certE (⟨98, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 16 else if j.val = 1 then 1 else if j.val = 2 then -3 else -8)) := by decide +kernel
  have hp : parent2 (⟨98, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨98, by omega⟩ : Fin 1104)).2.2 = 272837776 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_99 :
    ((certNum ⟨99, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨99, by omega⟩) ⟨99, by omega⟩ (certE ⟨99, by omega⟩) := by
  have hm : certMode (⟨99, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨99, by omega⟩ : Fin 1104) = 203945631676981996025951975591 := by decide +kernel
  have he : certE (⟨99, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨99, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨99, by omega⟩ : Fin 1104)).2.2 = 21076532873 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_100 :
    ((certNum ⟨100, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨100, by omega⟩) ⟨100, by omega⟩ (certE ⟨100, by omega⟩) := by
  have hm : certMode (⟨100, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨100, by omega⟩ : Fin 1104) = 10498249052010044382811100385 := by decide +kernel
  have he : certE (⟨100, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 9 else if j.val = 1 then -5 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hp : parent2 (⟨100, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨100, by omega⟩ : Fin 1104)).2.2 = 626819267 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_101 :
    ((certNum ⟨101, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨101, by omega⟩) ⟨101, by omega⟩ (certE ⟨101, by omega⟩) := by
  have hm : certMode (⟨101, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨101, by omega⟩ : Fin 1104) = 203945858960123686661722067912 := by decide +kernel
  have he : certE (⟨101, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨101, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨101, by omega⟩ : Fin 1104)).2.2 = 21076562650 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_102 :
    ((certNum ⟨102, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨102, by omega⟩) ⟨102, by omega⟩ (certE ⟨102, by omega⟩) := by
  have hm : certMode (⟨102, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨102, by omega⟩ : Fin 1104) = 5024335382923303612178790089 := by decide +kernel
  have he : certE (⟨102, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -36 else if j.val = 1 then 7 else if j.val = 2 then 2 else 3)) := by decide +kernel
  have hp : parent2 (⟨102, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨102, by omega⟩ : Fin 1104)).2.2 = 272877465 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_103 :
    ((certNum ⟨103, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨103, by omega⟩) ⟨103, by omega⟩ (certE ⟨103, by omega⟩) := by
  have hm : certMode (⟨103, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨103, by omega⟩ : Fin 1104) = 203945832061996998360700870158 := by decide +kernel
  have he : certE (⟨103, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨103, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨103, by omega⟩ : Fin 1104)).2.2 = 21076559126 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_104 :
    ((certNum ⟨104, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨104, by omega⟩) ⟨104, by omega⟩ (certE ⟨104, by omega⟩) := by
  have hm : certMode (⟨104, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨104, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨104, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨104, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨104, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_105 :
    ((certNum ⟨105, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨105, by omega⟩) ⟨105, by omega⟩ (certE ⟨105, by omega⟩) := by
  have hm : certMode (⟨105, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨105, by omega⟩ : Fin 1104) = 190769826628246276719152283013 := by decide +kernel
  have he : certE (⟨105, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨105, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨105, by omega⟩ : Fin 1104)).2.2 = 19369793621 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_106 :
    ((certNum ⟨106, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨106, by omega⟩) ⟨106, by omega⟩ (certE ⟨106, by omega⟩) := by
  have hm : certMode (⟨106, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨106, by omega⟩ : Fin 1104) = 203945842129712695650894834910 := by decide +kernel
  have he : certE (⟨106, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨106, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨106, by omega⟩ : Fin 1104)).2.2 = 21076560445 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_107 :
    ((certNum ⟨107, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨107, by omega⟩) ⟨107, by omega⟩ (certE ⟨107, by omega⟩) := by
  have hm : certMode (⟨107, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨107, by omega⟩ : Fin 1104) = 89107591176877030411350700431 := by decide +kernel
  have he : certE (⟨107, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 7 else if j.val = 1 then -3 else if j.val = 2 then -4 else 0)) := by decide +kernel
  have hp : parent2 (⟨107, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨107, by omega⟩ : Fin 1104)).2.2 = 7584962385 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_108 :
    ((certNum ⟨108, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨108, by omega⟩) ⟨108, by omega⟩ (certE ⟨108, by omega⟩) := by
  have hm : certMode (⟨108, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨108, by omega⟩ : Fin 1104) = 181437533678316959048237291885 := by decide +kernel
  have he : certE (⟨108, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hp : parent2 (⟨108, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨108, by omega⟩ : Fin 1104)).2.2 = 18184590222 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_109 :
    ((certNum ⟨109, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨109, by omega⟩) ⟨109, by omega⟩ (certE ⟨109, by omega⟩) := by
  have hm : certMode (⟨109, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨109, by omega⟩ : Fin 1104) = 203945840587879078237384615672 := by decide +kernel
  have he : certE (⟨109, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨109, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨109, by omega⟩ : Fin 1104)).2.2 = 21076560243 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_110 :
    ((certNum ⟨110, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨110, by omega⟩) ⟨110, by omega⟩ (certE ⟨110, by omega⟩) := by
  have hm : certMode (⟨110, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨110, by omega⟩ : Fin 1104) = 202779409120887284729104126331 := by decide +kernel
  have he : certE (⟨110, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨110, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨110, by omega⟩ : Fin 1104)).2.2 = 20923898199 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_111 :
    ((certNum ⟨111, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨111, by omega⟩) ⟨111, by omega⟩ (certE ⟨111, by omega⟩) := by
  have hm : certMode (⟨111, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨111, by omega⟩ : Fin 1104) = 180933405777360015011547959588 := by decide +kernel
  have he : certE (⟨111, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then -33 else if j.val = 1 then 3 else if j.val = 2 then 0 else 8)) := by decide +kernel
  have hp : parent2 (⟨111, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨111, by omega⟩ : Fin 1104)).2.2 = 18121129290 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_112 :
    ((certNum ⟨112, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨112, by omega⟩) ⟨112, by omega⟩ (certE ⟨112, by omega⟩) := by
  have hm : certMode (⟨112, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨112, by omega⟩ : Fin 1104) = 91639493226739672743870506574 := by decide +kernel
  have he : certE (⟨112, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -8 else if j.val = 1 then -4 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨112, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨112, by omega⟩ : Fin 1104)).2.2 = 7846036071 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_113 :
    ((certNum ⟨113, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨113, by omega⟩) ⟨113, by omega⟩ (certE ⟨113, by omega⟩) := by
  have hm : certMode (⟨113, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨113, by omega⟩ : Fin 1104) = 202779417824489557517187054893 := by decide +kernel
  have he : certE (⟨113, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨113, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨113, by omega⟩ : Fin 1104)).2.2 = 20923899337 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_114 :
    ((certNum ⟨114, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨114, by omega⟩) ⟨114, by omega⟩ (certE ⟨114, by omega⟩) := by
  have hm : certMode (⟨114, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨114, by omega⟩ : Fin 1104) = 190642033795911674845384850846 := by decide +kernel
  have he : certE (⟨114, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hp : parent2 (⟨114, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨114, by omega⟩ : Fin 1104)).2.2 = 19353430759 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_115 :
    ((certNum ⟨115, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨115, by omega⟩) ⟨115, by omega⟩ (certE ⟨115, by omega⟩) := by
  have hm : certMode (⟨115, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨115, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨115, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨115, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨115, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_116 :
    ((certNum ⟨116, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨116, by omega⟩) ⟨116, by omega⟩ (certE ⟨116, by omega⟩) := by
  have hm : certMode (⟨116, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨116, by omega⟩ : Fin 1104) = 181070440264373226657323121229 := by decide +kernel
  have he : certE (⟨116, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨116, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨116, by omega⟩ : Fin 1104)).2.2 = 18138373679 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_117 :
    ((certNum ⟨117, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨117, by omega⟩) ⟨117, by omega⟩ (certE ⟨117, by omega⟩) := by
  have hm : certMode (⟨117, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨117, by omega⟩ : Fin 1104) = 89953663825103155666269997073 := by decide +kernel
  have he : certE (⟨117, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -30 else if j.val = 1 then -7 else if j.val = 2 then 5 else 8)) := by decide +kernel
  have hp : parent2 (⟨117, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨117, by omega⟩ : Fin 1104)).2.2 = 7671998046 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_118 :
    ((certNum ⟨118, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨118, by omega⟩) ⟨118, by omega⟩ (certE ⟨118, by omega⟩) := by
  have hm : certMode (⟨118, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨118, by omega⟩ : Fin 1104) = 203945843579952229403717521043 := by decide +kernel
  have he : certE (⟨118, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨118, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨118, by omega⟩ : Fin 1104)).2.2 = 21076560635 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_119 :
    ((certNum ⟨119, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨119, by omega⟩) ⟨119, by omega⟩ (certE ⟨119, by omega⟩) := by
  have hm : certMode (⟨119, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨119, by omega⟩ : Fin 1104) = 190588906979785707016801013967 := by decide +kernel
  have he : certE (⟨119, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then -40 else if j.val = 1 then 4 else if j.val = 2 then 6 else 5)) := by decide +kernel
  have hp : parent2 (⟨119, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨119, by omega⟩ : Fin 1104)).2.2 = 19346629376 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_120 :
    ((certNum ⟨120, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨120, by omega⟩) ⟨120, by omega⟩ (certE ⟨120, by omega⟩) := by
  have hm : certMode (⟨120, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨120, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨120, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨120, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨120, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_121 :
    ((certNum ⟨121, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨121, by omega⟩) ⟨121, by omega⟩ (certE ⟨121, by omega⟩) := by
  have hm : certMode (⟨121, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨121, by omega⟩ : Fin 1104) = 203945846304875965582563926875 := by decide +kernel
  have he : certE (⟨121, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨121, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨121, by omega⟩ : Fin 1104)).2.2 = 21076560992 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_122 :
    ((certNum ⟨122, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨122, by omega⟩) ⟨122, by omega⟩ (certE ⟨122, by omega⟩) := by
  have hm : certMode (⟨122, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨122, by omega⟩ : Fin 1104) = 180791684532174544022765494594 := by decide +kernel
  have he : certE (⟨122, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hp : parent2 (⟨122, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨122, by omega⟩ : Fin 1104)).2.2 = 18103299789 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_123 :
    ((certNum ⟨123, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨123, by omega⟩) ⟨123, by omega⟩ (certE ⟨123, by omega⟩) := by
  have hm : certMode (⟨123, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨123, by omega⟩ : Fin 1104) = 203309852979771329737680753309 := by decide +kernel
  have he : certE (⟨123, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨123, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨123, by omega⟩ : Fin 1104)).2.2 = 20993285071 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_124 :
    ((certNum ⟨124, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨124, by omega⟩) ⟨124, by omega⟩ (certE ⟨124, by omega⟩) := by
  have hm : certMode (⟨124, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨124, by omega⟩ : Fin 1104) = 91300035234911052925340005364 := by decide +kernel
  have he : certE (⟨124, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -54 else if j.val = 1 then 7 else if j.val = 2 then 7 else 7)) := by decide +kernel
  have hp : parent2 (⟨124, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨124, by omega⟩ : Fin 1104)).2.2 = 7810925836 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_125 :
    ((certNum ⟨125, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨125, by omega⟩) ⟨125, by omega⟩ (certE ⟨125, by omega⟩) := by
  have hm : certMode (⟨125, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨125, by omega⟩ : Fin 1104) = 190504912327587242640369964927 := by decide +kernel
  have he : certE (⟨125, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 13 else if j.val = 1 then 5 else if j.val = 2 then -3 else -7)) := by decide +kernel
  have hp : parent2 (⟨125, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨125, by omega⟩ : Fin 1104)).2.2 = 19335877605 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_126 :
    ((certNum ⟨126, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨126, by omega⟩) ⟨126, by omega⟩ (certE ⟨126, by omega⟩) := by
  have hm : certMode (⟨126, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨126, by omega⟩ : Fin 1104) = 203309840546772024411885366813 := by decide +kernel
  have he : certE (⟨126, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨126, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨126, by omega⟩ : Fin 1104)).2.2 = 20993283444 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_127 :
    ((certNum ⟨127, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨127, by omega⟩) ⟨127, by omega⟩ (certE ⟨127, by omega⟩) := by
  have hm : certMode (⟨127, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨127, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨127, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨127, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨127, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_128 :
    ((certNum ⟨128, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨128, by omega⟩) ⟨128, by omega⟩ (certE ⟨128, by omega⟩) := by
  have hm : certMode (⟨128, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨128, by omega⟩ : Fin 1104) = 18320942691485207275183925273 := by decide +kernel
  have he : certE (⟨128, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -35 else if j.val = 1 then 6 else if j.val = 2 then 8 else -1)) := by decide +kernel
  have hp : parent2 (⟨128, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨128, by omega⟩ : Fin 1104)).2.2 = 1183861648 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_129 :
    ((certNum ⟨129, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨129, by omega⟩) ⟨129, by omega⟩ (certE ⟨129, by omega⟩) := by
  have hm : certMode (⟨129, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨129, by omega⟩ : Fin 1104) = 203945857876260513541543789144 := by decide +kernel
  have he : certE (⟨129, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨129, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨129, by omega⟩ : Fin 1104)).2.2 = 21076562508 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_130 :
    ((certNum ⟨130, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨130, by omega⟩) ⟨130, by omega⟩ (certE ⟨130, by omega⟩) := by
  have hm : certMode (⟨130, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨130, by omega⟩ : Fin 1104) = 10367586798529251234479304592 := by decide +kernel
  have he : certE (⟨130, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -17 else if j.val = 1 then 4 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨130, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨130, by omega⟩ : Fin 1104)).2.2 = 617967745 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_131 :
    ((certNum ⟨131, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨131, by omega⟩) ⟨131, by omega⟩ (certE ⟨131, by omega⟩) := by
  have hm : certMode (⟨131, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨131, by omega⟩ : Fin 1104) = 203945806316426782287314595758 := by decide +kernel
  have he : certE (⟨131, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨131, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨131, by omega⟩ : Fin 1104)).2.2 = 21076555753 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_132 :
    ((certNum ⟨132, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨132, by omega⟩) ⟨132, by omega⟩ (certE ⟨132, by omega⟩) := by
  have hm : certMode (⟨132, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨132, by omega⟩ : Fin 1104) = 10368487421414819033138078219 := by decide +kernel
  have he : certE (⟨132, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -17 else if j.val = 1 then 4 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨132, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨132, by omega⟩ : Fin 1104)).2.2 = 618028698 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_133 :
    ((certNum ⟨133, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨133, by omega⟩) ⟨133, by omega⟩ (certE ⟨133, by omega⟩) := by
  have hm : certMode (⟨133, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨133, by omega⟩ : Fin 1104) = 203945843579952229403717521043 := by decide +kernel
  have he : certE (⟨133, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨133, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨133, by omega⟩ : Fin 1104)).2.2 = 21076560635 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_134 :
    ((certNum ⟨134, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨134, by omega⟩) ⟨134, by omega⟩ (certE ⟨134, by omega⟩) := by
  have hm : certMode (⟨134, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨134, by omega⟩ : Fin 1104) = 202779539437801489906644513617 := by decide +kernel
  have he : certE (⟨134, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨134, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨134, by omega⟩ : Fin 1104)).2.2 = 20923915238 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_135 :
    ((certNum ⟨135, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨135, by omega⟩) ⟨135, by omega⟩ (certE ⟨135, by omega⟩) := by
  have hm : certMode (⟨135, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨135, by omega⟩ : Fin 1104) = 15881014083619983493713306303 := by decide +kernel
  have he : certE (⟨135, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then -3 else 3)) := by decide +kernel
  have hp : parent2 (⟨135, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨135, by omega⟩ : Fin 1104)).2.2 = 1004889316 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_136 :
    ((certNum ⟨136, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨136, by omega⟩) ⟨136, by omega⟩ (certE ⟨136, by omega⟩) := by
  have hm : certMode (⟨136, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨136, by omega⟩ : Fin 1104) = 202779464417055502338958720014 := by decide +kernel
  have he : certE (⟨136, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨136, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨136, by omega⟩ : Fin 1104)).2.2 = 20923905429 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_137 :
    ((certNum ⟨137, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨137, by omega⟩) ⟨137, by omega⟩ (certE ⟨137, by omega⟩) := by
  have hm : certMode (⟨137, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨137, by omega⟩ : Fin 1104) = 25545848228441090453289683655 := by decide +kernel
  have he : certE (⟨137, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -11 else if j.val = 1 then -3 else if j.val = 2 then -2 else 4)) := by decide +kernel
  have hp : parent2 (⟨137, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨137, by omega⟩ : Fin 1104)).2.2 = 1736885894 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_138 :
    ((certNum ⟨138, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨138, by omega⟩) ⟨138, by omega⟩ (certE ⟨138, by omega⟩) := by
  have hm : certMode (⟨138, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨138, by omega⟩ : Fin 1104) = 202779615590454685815752355864 := by decide +kernel
  have he : certE (⟨138, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨138, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨138, by omega⟩ : Fin 1104)).2.2 = 20923925195 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_139 :
    ((certNum ⟨139, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨139, by omega⟩) ⟨139, by omega⟩ (certE ⟨139, by omega⟩) := by
  have hm : certMode (⟨139, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨139, by omega⟩ : Fin 1104) = 15881749254375275320745983902 := by decide +kernel
  have he : certE (⟨139, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -14 else if j.val = 1 then 5 else if j.val = 2 then 8 else -8)) := by decide +kernel
  have hp : parent2 (⟨139, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨139, by omega⟩ : Fin 1104)).2.2 = 1004942583 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_140 :
    ((certNum ⟨140, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨140, by omega⟩) ⟨140, by omega⟩ (certE ⟨140, by omega⟩) := by
  have hm : certMode (⟨140, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨140, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨140, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨140, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨140, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_141 :
    ((certNum ⟨141, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨141, by omega⟩) ⟨141, by omega⟩ (certE ⟨141, by omega⟩) := by
  have hm : certMode (⟨141, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨141, by omega⟩ : Fin 1104) = 3077860867031867648773995 := by decide +kernel
  have he : certE (⟨141, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -10 else if j.val = 1 then -7 else if j.val = 2 then -1 else 0)) := by decide +kernel
  have hp : parent2 (⟨141, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨141, by omega⟩ : Fin 1104)).2.2 = 89311 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_142 :
    ((certNum ⟨142, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨142, by omega⟩) ⟨142, by omega⟩ (certE ⟨142, by omega⟩) := by
  have hm : certMode (⟨142, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨142, by omega⟩ : Fin 1104) = 203945823787998396203340067648 := by decide +kernel
  have he : certE (⟨142, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨142, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨142, by omega⟩ : Fin 1104)).2.2 = 21076558042 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_143 :
    ((certNum ⟨143, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨143, by omega⟩) ⟨143, by omega⟩ (certE ⟨143, by omega⟩) := by
  have hm : certMode (⟨143, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨143, by omega⟩ : Fin 1104) = 3058314506537504542357400 := by decide +kernel
  have he : certE (⟨143, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -30 else if j.val = 1 then 5 else if j.val = 2 then -3 else 2)) := by decide +kernel
  have hp : parent2 (⟨143, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨143, by omega⟩ : Fin 1104)).2.2 = 88709 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_144 :
    ((certNum ⟨144, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨144, by omega⟩) ⟨144, by omega⟩ (certE ⟨144, by omega⟩) := by
  have hm : certMode (⟨144, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨144, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨144, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨144, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨144, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_145 :
    ((certNum ⟨145, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨145, by omega⟩) ⟨145, by omega⟩ (certE ⟨145, by omega⟩) := by
  have hm : certMode (⟨145, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨145, by omega⟩ : Fin 1104) = 203945824162007563133287236193 := by decide +kernel
  have he : certE (⟨145, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨145, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨145, by omega⟩ : Fin 1104)).2.2 = 21076558091 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_146 :
    ((certNum ⟨146, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨146, by omega⟩) ⟨146, by omega⟩ (certE ⟨146, by omega⟩) := by
  have hm : certMode (⟨146, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨146, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨146, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨146, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨146, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_147 :
    ((certNum ⟨147, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨147, by omega⟩) ⟨147, by omega⟩ (certE ⟨147, by omega⟩) := by
  have hm : certMode (⟨147, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨147, by omega⟩ : Fin 1104) = 203879221577279193900552550818 := by decide +kernel
  have he : certE (⟨147, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨147, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨147, by omega⟩ : Fin 1104)).2.2 = 21067832877 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_148 :
    ((certNum ⟨148, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨148, by omega⟩) ⟨148, by omega⟩ (certE ⟨148, by omega⟩) := by
  have hm : certMode (⟨148, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨148, by omega⟩ : Fin 1104) = 177418267363947731446577501233 := by decide +kernel
  have he : certE (⟨148, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 18 else if j.val = 1 then 5 else if j.val = 2 then -4 else -8)) := by decide +kernel
  have hp : parent2 (⟨148, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨148, by omega⟩ : Fin 1104)).2.2 = 17680247127 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_149 :
    ((certNum ⟨149, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨149, by omega⟩) ⟨149, by omega⟩ (certE ⟨149, by omega⟩) := by
  have hm : certMode (⟨149, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨149, by omega⟩ : Fin 1104) = 203783259422029818257171755004 := by decide +kernel
  have he : certE (⟨149, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨149, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨149, by omega⟩ : Fin 1104)).2.2 = 21055263198 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_150 :
    ((certNum ⟨150, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨150, by omega⟩) ⟨150, by omega⟩ (certE ⟨150, by omega⟩) := by
  have hm : certMode (⟨150, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨150, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨150, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨150, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨150, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_151 :
    ((certNum ⟨151, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨151, by omega⟩) ⟨151, by omega⟩ (certE ⟨151, by omega⟩) := by
  have hm : certMode (⟨151, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨151, by omega⟩ : Fin 1104) = 177445711929229648941135151454 := by decide +kernel
  have he : certE (⟨151, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 17 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨151, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨151, by omega⟩ : Fin 1104)).2.2 = 17683678425 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_152 :
    ((certNum ⟨152, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨152, by omega⟩) ⟨152, by omega⟩ (certE ⟨152, by omega⟩) := by
  have hm : certMode (⟨152, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨152, by omega⟩ : Fin 1104) = 203309785794190454626963811485 := by decide +kernel
  have he : certE (⟨152, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨152, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨152, by omega⟩ : Fin 1104)).2.2 = 20993276279 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_153 :
    ((certNum ⟨153, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨153, by omega⟩) ⟨153, by omega⟩ (certE ⟨153, by omega⟩) := by
  have hm : certMode (⟨153, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨153, by omega⟩ : Fin 1104) = 25353796418091331308654002013 := by decide +kernel
  have he : certE (⟨153, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -6 else if j.val = 1 then 3 else if j.val = 2 then -1 else -2)) := by decide +kernel
  have hp : parent2 (⟨153, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨153, by omega⟩ : Fin 1104)).2.2 = 1721779424 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_154 :
    ((certNum ⟨154, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨154, by omega⟩) ⟨154, by omega⟩ (certE ⟨154, by omega⟩) := by
  have hm : certMode (⟨154, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨154, by omega⟩ : Fin 1104) = 203309794864856104150802463914 := by decide +kernel
  have he : certE (⟨154, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨154, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨154, by omega⟩ : Fin 1104)).2.2 = 20993277466 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_155 :
    ((certNum ⟨155, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨155, by omega⟩) ⟨155, by omega⟩ (certE ⟨155, by omega⟩) := by
  have hm : certMode (⟨155, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨155, by omega⟩ : Fin 1104) = 15737541078983960290113365084 := by decide +kernel
  have he : certE (⟨155, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 13 else if j.val = 1 then 7 else if j.val = 2 then -5 else -8)) := by decide +kernel
  have hp : parent2 (⟨155, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨155, by omega⟩ : Fin 1104)).2.2 = 994501850 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_156 :
    ((certNum ⟨156, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨156, by omega⟩) ⟨156, by omega⟩ (certE ⟨156, by omega⟩) := by
  have hm : certMode (⟨156, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨156, by omega⟩ : Fin 1104) = 203309779100084875616653043080 := by decide +kernel
  have he : certE (⟨156, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨156, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨156, by omega⟩ : Fin 1104)).2.2 = 20993275403 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_157 :
    ((certNum ⟨157, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨157, by omega⟩) ⟨157, by omega⟩ (certE ⟨157, by omega⟩) := by
  have hm : certMode (⟨157, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨157, by omega⟩ : Fin 1104) = 15738481754618435848582365081 := by decide +kernel
  have he : certE (⟨157, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -35 else if j.val = 1 then 7 else if j.val = 2 then 6 else 0)) := by decide +kernel
  have hp : parent2 (⟨157, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨157, by omega⟩ : Fin 1104)).2.2 = 994569904 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_158 :
    ((certNum ⟨158, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨158, by omega⟩) ⟨158, by omega⟩ (certE ⟨158, by omega⟩) := by
  have hm : certMode (⟨158, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨158, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨158, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨158, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨158, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_159 :
    ((certNum ⟨159, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨159, by omega⟩) ⟨159, by omega⟩ (certE ⟨159, by omega⟩) := by
  have hm : certMode (⟨159, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨159, by omega⟩ : Fin 1104) = 203945804568506279732750004094 := by decide +kernel
  have he : certE (⟨159, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨159, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨159, by omega⟩ : Fin 1104)).2.2 = 21076555524 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_160 :
    ((certNum ⟨160, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨160, by omega⟩) ⟨160, by omega⟩ (certE ⟨160, by omega⟩) := by
  have hm : certMode (⟨160, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨160, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨160, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨160, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨160, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_161 :
    ((certNum ⟨161, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨161, by omega⟩) ⟨161, by omega⟩ (certE ⟨161, by omega⟩) := by
  have hm : certMode (⟨161, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨161, by omega⟩ : Fin 1104) = 203945814323276462484512413319 := by decide +kernel
  have he : certE (⟨161, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨161, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨161, by omega⟩ : Fin 1104)).2.2 = 21076556802 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_162 :
    ((certNum ⟨162, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨162, by omega⟩) ⟨162, by omega⟩ (certE ⟨162, by omega⟩) := by
  have hm : certMode (⟨162, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨162, by omega⟩ : Fin 1104) = 203782883373884727689927467961 := by decide +kernel
  have he : certE (⟨162, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨162, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨162, by omega⟩ : Fin 1104)).2.2 = 21055213946 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_163 :
    ((certNum ⟨163, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨163, by omega⟩) ⟨163, by omega⟩ (certE ⟨163, by omega⟩) := by
  have hm : certMode (⟨163, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨163, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨163, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨163, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨163, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_164 :
    ((certNum ⟨164, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨164, by omega⟩) ⟨164, by omega⟩ (certE ⟨164, by omega⟩) := by
  have hm : certMode (⟨164, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨164, by omega⟩ : Fin 1104) = 203783472542742778749209756138 := by decide +kernel
  have he : certE (⟨164, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨164, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨164, by omega⟩ : Fin 1104)).2.2 = 21055291111 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_165 :
    ((certNum ⟨165, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨165, by omega⟩) ⟨165, by omega⟩ (certE ⟨165, by omega⟩) := by
  have hm : certMode (⟨165, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨165, by omega⟩ : Fin 1104) = 39812496334840486527248267888 := by decide +kernel
  have he : certE (⟨165, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -36 else if j.val = 1 then 5 else if j.val = 2 then 0 else 7)) := by decide +kernel
  have hp : parent2 (⟨165, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨165, by omega⟩ : Fin 1104)).2.2 = 2911969781 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_166 :
    ((certNum ⟨166, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨166, by omega⟩) ⟨166, by omega⟩ (certE ⟨166, by omega⟩) := by
  have hm : certMode (⟨166, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨166, by omega⟩ : Fin 1104) = 203782876792350738442017660155 := by decide +kernel
  have he : certE (⟨166, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨166, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨166, by omega⟩ : Fin 1104)).2.2 = 21055213084 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_167 :
    ((certNum ⟨167, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨167, by omega⟩) ⟨167, by omega⟩ (certE ⟨167, by omega⟩) := by
  have hm : certMode (⟨167, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨167, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨167, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨167, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨167, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_168 :
    ((certNum ⟨168, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨168, by omega⟩) ⟨168, by omega⟩ (certE ⟨168, by omega⟩) := by
  have hm : certMode (⟨168, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨168, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨168, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨168, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨168, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_169 :
    ((certNum ⟨169, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨169, by omega⟩) ⟨169, by omega⟩ (certE ⟨169, by omega⟩) := by
  have hm : certMode (⟨169, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨169, by omega⟩ : Fin 1104) = 203945803034305306045860424644 := by decide +kernel
  have he : certE (⟨169, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨169, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨169, by omega⟩ : Fin 1104)).2.2 = 21076555323 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_170 :
    ((certNum ⟨170, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨170, by omega⟩) ⟨170, by omega⟩ (certE ⟨170, by omega⟩) := by
  have hm : certMode (⟨170, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨170, by omega⟩ : Fin 1104) = 203873172819857009722120081758 := by decide +kernel
  have he : certE (⟨170, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨170, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨170, by omega⟩ : Fin 1104)).2.2 = 21067040498 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_171 :
    ((certNum ⟨171, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨171, by omega⟩) ⟨171, by omega⟩ (certE ⟨171, by omega⟩) := by
  have hm : certMode (⟨171, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨171, by omega⟩ : Fin 1104) = 39748161597905065888069915152 := by decide +kernel
  have he : certE (⟨171, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -11 else if j.val = 1 then -1 else if j.val = 2 then 3 else -1)) := by decide +kernel
  have hp : parent2 (⟨171, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨171, by omega⟩ : Fin 1104)).2.2 = 2906456017 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_172 :
    ((certNum ⟨172, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨172, by omega⟩) ⟨172, by omega⟩ (certE ⟨172, by omega⟩) := by
  have hm : certMode (⟨172, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨172, by omega⟩ : Fin 1104) = 203875822900843239189481287590 := by decide +kernel
  have he : certE (⟨172, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨172, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨172, by omega⟩ : Fin 1104)).2.2 = 21067387653 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_173 :
    ((certNum ⟨173, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨173, by omega⟩) ⟨173, by omega⟩ (certE ⟨173, by omega⟩) := by
  have hm : certMode (⟨173, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨173, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨173, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨173, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨173, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_174 :
    ((certNum ⟨174, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨174, by omega⟩) ⟨174, by omega⟩ (certE ⟨174, by omega⟩) := by
  have hm : certMode (⟨174, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨174, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨174, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨174, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨174, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_175 :
    ((certNum ⟨175, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨175, by omega⟩) ⟨175, by omega⟩ (certE ⟨175, by omega⟩) := by
  have hm : certMode (⟨175, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨175, by omega⟩ : Fin 1104) = 203945812926466667435481467284 := by decide +kernel
  have he : certE (⟨175, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨175, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨175, by omega⟩ : Fin 1104)).2.2 = 21076556619 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_176 :
    ((certNum ⟨176, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨176, by omega⟩) ⟨176, by omega⟩ (certE ⟨176, by omega⟩) := by
  have hm : certMode (⟨176, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨176, by omega⟩ : Fin 1104) = 203876453357893652168251463671 := by decide +kernel
  have he : certE (⟨176, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨176, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨176, by omega⟩ : Fin 1104)).2.2 = 21067470242 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_177 :
    ((certNum ⟨177, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨177, by omega⟩) ⟨177, by omega⟩ (certE ⟨177, by omega⟩) := by
  have hm : certMode (⟨177, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨177, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨177, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨177, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨177, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_178 :
    ((certNum ⟨178, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨178, by omega⟩) ⟨178, by omega⟩ (certE ⟨178, by omega⟩) := by
  have hm : certMode (⟨178, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨178, by omega⟩ : Fin 1104) = 203948760302494539580960324671 := by decide +kernel
  have he : certE (⟨178, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨178, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨178, by omega⟩ : Fin 1104)).2.2 = 21076942765 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_179 :
    ((certNum ⟨179, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨179, by omega⟩) ⟨179, by omega⟩ (certE ⟨179, by omega⟩) := by
  have hm : certMode (⟨179, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨179, by omega⟩ : Fin 1104) = 203948760294861775663214677769 := by decide +kernel
  have he : certE (⟨179, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨179, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨179, by omega⟩ : Fin 1104)).2.2 = 21076942764 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_180 :
    ((certNum ⟨180, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨180, by omega⟩) ⟨180, by omega⟩ (certE ⟨180, by omega⟩) := by
  have hm : certMode (⟨180, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨180, by omega⟩ : Fin 1104) = 203948758722512404383089529776 := by decide +kernel
  have he : certE (⟨180, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨180, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨180, by omega⟩ : Fin 1104)).2.2 = 21076942558 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_181 :
    ((certNum ⟨181, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨181, by omega⟩) ⟨181, by omega⟩ (certE ⟨181, by omega⟩) := by
  have hm : certMode (⟨181, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨181, by omega⟩ : Fin 1104) = 203948747273366243484670935610 := by decide +kernel
  have he : certE (⟨181, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨181, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨181, by omega⟩ : Fin 1104)).2.2 = 21076941058 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_182 :
    ((certNum ⟨182, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨182, by omega⟩) ⟨182, by omega⟩ (certE ⟨182, by omega⟩) := by
  have hm : certMode (⟨182, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨182, by omega⟩ : Fin 1104) = 203948758669083056667605653034 := by decide +kernel
  have he : certE (⟨182, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨182, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨182, by omega⟩ : Fin 1104)).2.2 = 21076942551 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_183 :
    ((certNum ⟨183, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨183, by omega⟩) ⟨183, by omega⟩ (certE ⟨183, by omega⟩) := by
  have hm : certMode (⟨183, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨183, by omega⟩ : Fin 1104) = 203948747525247463820490012733 := by decide +kernel
  have he : certE (⟨183, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨183, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨183, by omega⟩ : Fin 1104)).2.2 = 21076941091 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨92 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨92 + j.val, by omega⟩) ⟨92 + j.val, by omega⟩
        (certE ⟨92 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_92
  | ⟨1, _⟩ => exact MME.L2Cert.cert_93
  | ⟨2, _⟩ => exact MME.L2Cert.cert_94
  | ⟨3, _⟩ => exact MME.L2Cert.cert_95
  | ⟨4, _⟩ => exact MME.L2Cert.cert_96
  | ⟨5, _⟩ => exact MME.L2Cert.cert_97
  | ⟨6, _⟩ => exact MME.L2Cert.cert_98
  | ⟨7, _⟩ => exact MME.L2Cert.cert_99
  | ⟨8, _⟩ => exact MME.L2Cert.cert_100
  | ⟨9, _⟩ => exact MME.L2Cert.cert_101
  | ⟨10, _⟩ => exact MME.L2Cert.cert_102
  | ⟨11, _⟩ => exact MME.L2Cert.cert_103
  | ⟨12, _⟩ => exact MME.L2Cert.cert_104
  | ⟨13, _⟩ => exact MME.L2Cert.cert_105
  | ⟨14, _⟩ => exact MME.L2Cert.cert_106
  | ⟨15, _⟩ => exact MME.L2Cert.cert_107
  | ⟨16, _⟩ => exact MME.L2Cert.cert_108
  | ⟨17, _⟩ => exact MME.L2Cert.cert_109
  | ⟨18, _⟩ => exact MME.L2Cert.cert_110
  | ⟨19, _⟩ => exact MME.L2Cert.cert_111
  | ⟨20, _⟩ => exact MME.L2Cert.cert_112
  | ⟨21, _⟩ => exact MME.L2Cert.cert_113
  | ⟨22, _⟩ => exact MME.L2Cert.cert_114
  | ⟨23, _⟩ => exact MME.L2Cert.cert_115
  | ⟨24, _⟩ => exact MME.L2Cert.cert_116
  | ⟨25, _⟩ => exact MME.L2Cert.cert_117
  | ⟨26, _⟩ => exact MME.L2Cert.cert_118
  | ⟨27, _⟩ => exact MME.L2Cert.cert_119
  | ⟨28, _⟩ => exact MME.L2Cert.cert_120
  | ⟨29, _⟩ => exact MME.L2Cert.cert_121
  | ⟨30, _⟩ => exact MME.L2Cert.cert_122
  | ⟨31, _⟩ => exact MME.L2Cert.cert_123
  | ⟨32, _⟩ => exact MME.L2Cert.cert_124
  | ⟨33, _⟩ => exact MME.L2Cert.cert_125
  | ⟨34, _⟩ => exact MME.L2Cert.cert_126
  | ⟨35, _⟩ => exact MME.L2Cert.cert_127
  | ⟨36, _⟩ => exact MME.L2Cert.cert_128
  | ⟨37, _⟩ => exact MME.L2Cert.cert_129
  | ⟨38, _⟩ => exact MME.L2Cert.cert_130
  | ⟨39, _⟩ => exact MME.L2Cert.cert_131
  | ⟨40, _⟩ => exact MME.L2Cert.cert_132
  | ⟨41, _⟩ => exact MME.L2Cert.cert_133
  | ⟨42, _⟩ => exact MME.L2Cert.cert_134
  | ⟨43, _⟩ => exact MME.L2Cert.cert_135
  | ⟨44, _⟩ => exact MME.L2Cert.cert_136
  | ⟨45, _⟩ => exact MME.L2Cert.cert_137
  | ⟨46, _⟩ => exact MME.L2Cert.cert_138
  | ⟨47, _⟩ => exact MME.L2Cert.cert_139
  | ⟨48, _⟩ => exact MME.L2Cert.cert_140
  | ⟨49, _⟩ => exact MME.L2Cert.cert_141
  | ⟨50, _⟩ => exact MME.L2Cert.cert_142
  | ⟨51, _⟩ => exact MME.L2Cert.cert_143
  | ⟨52, _⟩ => exact MME.L2Cert.cert_144
  | ⟨53, _⟩ => exact MME.L2Cert.cert_145
  | ⟨54, _⟩ => exact MME.L2Cert.cert_146
  | ⟨55, _⟩ => exact MME.L2Cert.cert_147
  | ⟨56, _⟩ => exact MME.L2Cert.cert_148
  | ⟨57, _⟩ => exact MME.L2Cert.cert_149
  | ⟨58, _⟩ => exact MME.L2Cert.cert_150
  | ⟨59, _⟩ => exact MME.L2Cert.cert_151
  | ⟨60, _⟩ => exact MME.L2Cert.cert_152
  | ⟨61, _⟩ => exact MME.L2Cert.cert_153
  | ⟨62, _⟩ => exact MME.L2Cert.cert_154
  | ⟨63, _⟩ => exact MME.L2Cert.cert_155
  | ⟨64, _⟩ => exact MME.L2Cert.cert_156
  | ⟨65, _⟩ => exact MME.L2Cert.cert_157
  | ⟨66, _⟩ => exact MME.L2Cert.cert_158
  | ⟨67, _⟩ => exact MME.L2Cert.cert_159
  | ⟨68, _⟩ => exact MME.L2Cert.cert_160
  | ⟨69, _⟩ => exact MME.L2Cert.cert_161
  | ⟨70, _⟩ => exact MME.L2Cert.cert_162
  | ⟨71, _⟩ => exact MME.L2Cert.cert_163
  | ⟨72, _⟩ => exact MME.L2Cert.cert_164
  | ⟨73, _⟩ => exact MME.L2Cert.cert_165
  | ⟨74, _⟩ => exact MME.L2Cert.cert_166
  | ⟨75, _⟩ => exact MME.L2Cert.cert_167
  | ⟨76, _⟩ => exact MME.L2Cert.cert_168
  | ⟨77, _⟩ => exact MME.L2Cert.cert_169
  | ⟨78, _⟩ => exact MME.L2Cert.cert_170
  | ⟨79, _⟩ => exact MME.L2Cert.cert_171
  | ⟨80, _⟩ => exact MME.L2Cert.cert_172
  | ⟨81, _⟩ => exact MME.L2Cert.cert_173
  | ⟨82, _⟩ => exact MME.L2Cert.cert_174
  | ⟨83, _⟩ => exact MME.L2Cert.cert_175
  | ⟨84, _⟩ => exact MME.L2Cert.cert_176
  | ⟨85, _⟩ => exact MME.L2Cert.cert_177
  | ⟨86, _⟩ => exact MME.L2Cert.cert_178
  | ⟨87, _⟩ => exact MME.L2Cert.cert_179
  | ⟨88, _⟩ => exact MME.L2Cert.cert_180
  | ⟨89, _⟩ => exact MME.L2Cert.cert_181
  | ⟨90, _⟩ => exact MME.L2Cert.cert_182
  | ⟨91, _⟩ => exact MME.L2Cert.cert_183
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
