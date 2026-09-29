-- Prove2me | solution 1 for mme_released_recursive_level2_cert0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T23:48:14.310467+00:00
-- url     : https://prove2.me/submissions/efeae3a0-6910-437a-b788-c0fc42801091

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

theorem cert_0 :
    ((certNum ⟨0, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨0, by omega⟩) ⟨0, by omega⟩ (certE ⟨0, by omega⟩) := by
  have hm : certMode (⟨0, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨0, by omega⟩ : Fin 1104) = 102317217068021218578559394 := by decide +kernel
  have he : certE (⟨0, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -3 else if j.val = 1 then 0 else if j.val = 2 then 2 else -7)) := by decide +kernel
  have hp : parent2 (⟨0, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨0, by omega⟩ : Fin 1104)).2.2 = 3794608 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_1 :
    ((certNum ⟨1, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨1, by omega⟩) ⟨1, by omega⟩ (certE ⟨1, by omega⟩) := by
  have hm : certMode (⟨1, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨1, by omega⟩ : Fin 1104) = 102347173250131558371877693 := by decide +kernel
  have he : certE (⟨1, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -8 else if j.val = 1 then -1 else if j.val = 2 then 0 else -3)) := by decide +kernel
  have hp : parent2 (⟨1, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨1, by omega⟩ : Fin 1104)).2.2 = 3795808 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_2 :
    ((certNum ⟨2, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨2, by omega⟩) ⟨2, by omega⟩ (certE ⟨2, by omega⟩) := by
  have hm : certMode (⟨2, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨2, by omega⟩ : Fin 1104) = 102316168586907342305140951 := by decide +kernel
  have he : certE (⟨2, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -3 else if j.val = 1 then 0 else if j.val = 2 then 2 else -7)) := by decide +kernel
  have hp : parent2 (⟨2, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨2, by omega⟩ : Fin 1104)).2.2 = 3794566 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_3 :
    ((certNum ⟨3, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨3, by omega⟩) ⟨3, by omega⟩ (certE ⟨3, by omega⟩) := by
  have hm : certMode (⟨3, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨3, by omega⟩ : Fin 1104) = 102343878122809758402770772 := by decide +kernel
  have he : certE (⟨3, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -4 else if j.val = 1 then -7 else if j.val = 2 then 6 else -6)) := by decide +kernel
  have hp : parent2 (⟨3, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨3, by omega⟩ : Fin 1104)).2.2 = 3795676 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_4 :
    ((certNum ⟨4, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨4, by omega⟩) ⟨4, by omega⟩ (certE ⟨4, by omega⟩) := by
  have hm : certMode (⟨4, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨4, by omega⟩ : Fin 1104) = 76409911901819675551356619 := by decide +kernel
  have he : certE (⟨4, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -17 else if j.val = 1 then -3 else if j.val = 2 then -1 else 2)) := by decide +kernel
  have hp : parent2 (⟨4, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨4, by omega⟩ : Fin 1104)).2.2 = 2769079 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_5 :
    ((certNum ⟨5, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨5, by omega⟩) ⟨5, by omega⟩ (certE ⟨5, by omega⟩) := by
  have hm : certMode (⟨5, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨5, by omega⟩ : Fin 1104) = 76409911901819675551356619 := by decide +kernel
  have he : certE (⟨5, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -17 else if j.val = 1 then -3 else if j.val = 2 then -1 else 2)) := by decide +kernel
  have hp : parent2 (⟨5, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨5, by omega⟩ : Fin 1104)).2.2 = 2769079 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_6 :
    ((certNum ⟨6, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨6, by omega⟩) ⟨6, by omega⟩ (certE ⟨6, by omega⟩) := by
  have hm : certMode (⟨6, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨6, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨6, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨6, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨6, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_7 :
    ((certNum ⟨7, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨7, by omega⟩) ⟨7, by omega⟩ (certE ⟨7, by omega⟩) := by
  have hm : certMode (⟨7, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨7, by omega⟩ : Fin 1104) = 203876903285490146827816727138 := by decide +kernel
  have he : certE (⟨7, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨7, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨7, by omega⟩ : Fin 1104)).2.2 = 21067529182 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_8 :
    ((certNum ⟨8, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨8, by omega⟩) ⟨8, by omega⟩ (certE ⟨8, by omega⟩) := by
  have hm : certMode (⟨8, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨8, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨8, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨8, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨8, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_9 :
    ((certNum ⟨9, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨9, by omega⟩) ⟨9, by omega⟩ (certE ⟨9, by omega⟩) := by
  have hm : certMode (⟨9, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨9, by omega⟩ : Fin 1104) = 203876389090100170604676595390 := by decide +kernel
  have he : certE (⟨9, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨9, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨9, by omega⟩ : Fin 1104)).2.2 = 21067461823 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_10 :
    ((certNum ⟨10, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨10, by omega⟩) ⟨10, by omega⟩ (certE ⟨10, by omega⟩) := by
  have hm : certMode (⟨10, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨10, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨10, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨10, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨10, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_11 :
    ((certNum ⟨11, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨11, by omega⟩) ⟨11, by omega⟩ (certE ⟨11, by omega⟩) := by
  have hm : certMode (⟨11, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨11, by omega⟩ : Fin 1104) = 203874324780336218548710503089 := by decide +kernel
  have he : certE (⟨11, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨11, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨11, by omega⟩ : Fin 1104)).2.2 = 21067191402 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_12 :
    ((certNum ⟨12, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨12, by omega⟩) ⟨12, by omega⟩ (certE ⟨12, by omega⟩) := by
  have hm : certMode (⟨12, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨12, by omega⟩ : Fin 1104) = 5081271977189557181088691565 := by decide +kernel
  have he : certE (⟨12, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 7 else if j.val = 1 then 4 else if j.val = 2 then -6 else -4)) := by decide +kernel
  have hp : parent2 (⟨12, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨12, by omega⟩ : Fin 1104)).2.2 = 276349353 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_13 :
    ((certNum ⟨13, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨13, by omega⟩) ⟨13, by omega⟩ (certE ⟨13, by omega⟩) := by
  have hm : certMode (⟨13, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨13, by omega⟩ : Fin 1104) = 203309791762336966593072446364 := by decide +kernel
  have he : certE (⟨13, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨13, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨13, by omega⟩ : Fin 1104)).2.2 = 20993277060 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_14 :
    ((certNum ⟨14, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨14, by omega⟩) ⟨14, by omega⟩ (certE ⟨14, by omega⟩) := by
  have hm : certMode (⟨14, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨14, by omega⟩ : Fin 1104) = 5080836056491512145203769443 := by decide +kernel
  have he : certE (⟨14, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 11 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨14, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨14, by omega⟩ : Fin 1104)).2.2 = 276322751 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_15 :
    ((certNum ⟨15, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨15, by omega⟩) ⟨15, by omega⟩ (certE ⟨15, by omega⟩) := by
  have hm : certMode (⟨15, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨15, by omega⟩ : Fin 1104) = 203310088213241649373771185987 := by decide +kernel
  have he : certE (⟨15, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨15, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨15, by omega⟩ : Fin 1104)).2.2 = 20993315854 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_16 :
    ((certNum ⟨16, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨16, by omega⟩) ⟨16, by omega⟩ (certE ⟨16, by omega⟩) := by
  have hm : certMode (⟨16, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨16, by omega⟩ : Fin 1104) = 10600119842886801167984878196 := by decide +kernel
  have he : certE (⟨16, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -26 else if j.val = 1 then 5 else if j.val = 2 then 2 else 1)) := by decide +kernel
  have hp : parent2 (⟨16, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨16, by omega⟩ : Fin 1104)).2.2 = 633732174 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_17 :
    ((certNum ⟨17, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨17, by omega⟩) ⟨17, by omega⟩ (certE ⟨17, by omega⟩) := by
  have hm : certMode (⟨17, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨17, by omega⟩ : Fin 1104) = 203309788720951179237609781037 := by decide +kernel
  have he : certE (⟨17, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨17, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨17, by omega⟩ : Fin 1104)).2.2 = 20993276662 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_18 :
    ((certNum ⟨18, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨18, by omega⟩) ⟨18, by omega⟩ (certE ⟨18, by omega⟩) := by
  have hm : certMode (⟨18, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨18, by omega⟩ : Fin 1104) = 202779562298131016056213951832 := by decide +kernel
  have he : certE (⟨18, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨18, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨18, by omega⟩ : Fin 1104)).2.2 = 20923918227 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_19 :
    ((certNum ⟨19, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨19, by omega⟩) ⟨19, by omega⟩ (certE ⟨19, by omega⟩) := by
  have hm : certMode (⟨19, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨19, by omega⟩ : Fin 1104) = 10582817020806098927099854509 := by decide +kernel
  have he : certE (⟨19, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -5 else if j.val = 1 then 5 else if j.val = 2 then -1 else -4)) := by decide +kernel
  have hp : parent2 (⟨19, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨19, by omega⟩ : Fin 1104)).2.2 = 632557285 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_20 :
    ((certNum ⟨20, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨20, by omega⟩) ⟨20, by omega⟩ (certE ⟨20, by omega⟩) := by
  have hm : certMode (⟨20, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨20, by omega⟩ : Fin 1104) = 202779679521345112249291481146 := by decide +kernel
  have he : certE (⟨20, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨20, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨20, by omega⟩ : Fin 1104)).2.2 = 20923933554 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_21 :
    ((certNum ⟨21, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨21, by omega⟩) ⟨21, by omega⟩ (certE ⟨21, by omega⟩) := by
  have hm : certMode (⟨21, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨21, by omega⟩ : Fin 1104) = 10583532200943396908497992986 := by decide +kernel
  have he : certE (⟨21, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -5 else if j.val = 1 then -6 else if j.val = 2 then -8 else 8)) := by decide +kernel
  have hp : parent2 (⟨21, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨21, by omega⟩ : Fin 1104)).2.2 = 632605841 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_22 :
    ((certNum ⟨22, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨22, by omega⟩) ⟨22, by omega⟩ (certE ⟨22, by omega⟩) := by
  have hm : certMode (⟨22, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨22, by omega⟩ : Fin 1104) = 202779461908460544878967701553 := by decide +kernel
  have he : certE (⟨22, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨22, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨22, by omega⟩ : Fin 1104)).2.2 = 20923905101 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_23 :
    ((certNum ⟨23, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨23, by omega⟩) ⟨23, by omega⟩ (certE ⟨23, by omega⟩) := by
  have hm : certMode (⟨23, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨23, by omega⟩ : Fin 1104) = 18639079342630232421004123003 := by decide +kernel
  have he : certE (⟨23, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -28 else if j.val = 1 then 3 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨23, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨23, by omega⟩ : Fin 1104)).2.2 = 1207509132 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_24 :
    ((certNum ⟨24, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨24, by omega⟩) ⟨24, by omega⟩ (certE ⟨24, by omega⟩) := by
  have hm : certMode (⟨24, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨24, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨24, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨24, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨24, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_25 :
    ((certNum ⟨25, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨25, by omega⟩) ⟨25, by omega⟩ (certE ⟨25, by omega⟩) := by
  have hm : certMode (⟨25, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨25, by omega⟩ : Fin 1104) = 180751605824529708282049057134 := by decide +kernel
  have he : certE (⟨25, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -18 else if j.val = 1 then 6 else if j.val = 2 then 6 else -4)) := by decide +kernel
  have hp : parent2 (⟨25, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨25, by omega⟩ : Fin 1104)).2.2 = 18098258238 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_26 :
    ((certNum ⟨26, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨26, by omega⟩) ⟨26, by omega⟩ (certE ⟨26, by omega⟩) := by
  have hm : certMode (⟨26, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨26, by omega⟩ : Fin 1104) = 203782889306427420025314862922 := by decide +kernel
  have he : certE (⟨26, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨26, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨26, by omega⟩ : Fin 1104)).2.2 = 21055214723 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_27 :
    ((certNum ⟨27, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨27, by omega⟩) ⟨27, by omega⟩ (certE ⟨27, by omega⟩) := by
  have hm : certMode (⟨27, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨27, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨27, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨27, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨27, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_28 :
    ((certNum ⟨28, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨28, by omega⟩) ⟨28, by omega⟩ (certE ⟨28, by omega⟩) := by
  have hm : certMode (⟨28, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨28, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨28, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨28, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨28, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_29 :
    ((certNum ⟨29, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨29, by omega⟩) ⟨29, by omega⟩ (certE ⟨29, by omega⟩) := by
  have hm : certMode (⟨29, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨29, by omega⟩ : Fin 1104) = 180756357957161674213747906572 := by decide +kernel
  have he : certE (⟨29, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -18 else if j.val = 1 then -5 else if j.val = 2 then -1 else 8)) := by decide +kernel
  have hp : parent2 (⟨29, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨29, by omega⟩ : Fin 1104)).2.2 = 18098855993 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_30 :
    ((certNum ⟨30, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨30, by omega⟩) ⟨30, by omega⟩ (certE ⟨30, by omega⟩) := by
  have hm : certMode (⟨30, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨30, by omega⟩ : Fin 1104) = 203782876960324925614906156118 := by decide +kernel
  have he : certE (⟨30, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨30, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨30, by omega⟩ : Fin 1104)).2.2 = 21055213106 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_31 :
    ((certNum ⟨31, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨31, by omega⟩) ⟨31, by omega⟩ (certE ⟨31, by omega⟩) := by
  have hm : certMode (⟨31, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨31, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨31, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨31, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨31, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_32 :
    ((certNum ⟨32, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨32, by omega⟩) ⟨32, by omega⟩ (certE ⟨32, by omega⟩) := by
  have hm : certMode (⟨32, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨32, by omega⟩ : Fin 1104) = 203783202356686046309308335443 := by decide +kernel
  have he : certE (⟨32, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨32, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨32, by omega⟩ : Fin 1104)).2.2 = 21055255724 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_33 :
    ((certNum ⟨33, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨33, by omega⟩) ⟨33, by omega⟩ (certE ⟨33, by omega⟩) := by
  have hm : certMode (⟨33, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨33, by omega⟩ : Fin 1104) = 173800795672590939606600463 := by decide +kernel
  have he : certE (⟨33, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -24 else if j.val = 1 then 1 else if j.val = 2 then -5 else 6)) := by decide +kernel
  have hp : parent2 (⟨33, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨33, by omega⟩ : Fin 1104)).2.2 = 6731961 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_34 :
    ((certNum ⟨34, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨34, by omega⟩) ⟨34, by omega⟩ (certE ⟨34, by omega⟩) := by
  have hm : certMode (⟨34, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨34, by omega⟩ : Fin 1104) = 179130223515040892598276272589 := by decide +kernel
  have he : certE (⟨34, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-2 : Int) else if j.val = 1 then 3 else if j.val = 2 then 0 else -1) else (if j.val = 0 then -25 else if j.val = 1 then -7 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hp : parent2 (⟨34, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨34, by omega⟩ : Fin 1104)).2.2 = 17894614548 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_35 :
    ((certNum ⟨35, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨35, by omega⟩) ⟨35, by omega⟩ (certE ⟨35, by omega⟩) := by
  have hm : certMode (⟨35, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨35, by omega⟩ : Fin 1104) = 179131798529807038544260721014 := by decide +kernel
  have he : certE (⟨35, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-2 : Int) else if j.val = 1 then 3 else if j.val = 2 then 0 else -1) else (if j.val = 0 then -29 else if j.val = 1 then -1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨35, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨35, by omega⟩ : Fin 1104)).2.2 = 17894812076 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_36 :
    ((certNum ⟨36, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨36, by omega⟩) ⟨36, by omega⟩ (certE ⟨36, by omega⟩) := by
  have hm : certMode (⟨36, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨36, by omega⟩ : Fin 1104) = 179129988949107099962480664652 := by decide +kernel
  have he : certE (⟨36, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-2 : Int) else if j.val = 1 then 3 else if j.val = 2 then 0 else -1) else (if j.val = 0 then -25 else if j.val = 1 then -7 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hp : parent2 (⟨36, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨36, by omega⟩ : Fin 1104)).2.2 = 17894585129 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_37 :
    ((certNum ⟨37, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨37, by omega⟩) ⟨37, by omega⟩ (certE ⟨37, by omega⟩) := by
  have hm : certMode (⟨37, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨37, by omega⟩ : Fin 1104) = 179129999274509338963606735655 := by decide +kernel
  have he : certE (⟨37, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-2 : Int) else if j.val = 1 then 3 else if j.val = 2 then 0 else -1) else (if j.val = 0 then -25 else if j.val = 1 then -7 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hp : parent2 (⟨37, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨37, by omega⟩ : Fin 1104)).2.2 = 17894586424 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_38 :
    ((certNum ⟨38, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨38, by omega⟩) ⟨38, by omega⟩ (certE ⟨38, by omega⟩) := by
  have hm : certMode (⟨38, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨38, by omega⟩ : Fin 1104) = 179131796560326080733397268411 := by decide +kernel
  have he : certE (⟨38, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-2 : Int) else if j.val = 1 then 3 else if j.val = 2 then 0 else -1) else (if j.val = 0 then -29 else if j.val = 1 then -1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨38, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨38, by omega⟩ : Fin 1104)).2.2 = 17894811829 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_39 :
    ((certNum ⟨39, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨39, by omega⟩) ⟨39, by omega⟩ (certE ⟨39, by omega⟩) := by
  have hm : certMode (⟨39, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨39, by omega⟩ : Fin 1104) = 179130443667091488021459487447 := by decide +kernel
  have he : certE (⟨39, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-2 : Int) else if j.val = 1 then 3 else if j.val = 2 then 0 else -1) else (if j.val = 0 then -29 else if j.val = 1 then -1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨39, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨39, by omega⟩ : Fin 1104)).2.2 = 17894642158 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_40 :
    ((certNum ⟨40, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨40, by omega⟩) ⟨40, by omega⟩ (certE ⟨40, by omega⟩) := by
  have hm : certMode (⟨40, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨40, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨40, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨40, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨40, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_41 :
    ((certNum ⟨41, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨41, by omega⟩) ⟨41, by omega⟩ (certE ⟨41, by omega⟩) := by
  have hm : certMode (⟨41, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨41, by omega⟩ : Fin 1104) = 203946850929870009775630484103 := by decide +kernel
  have he : certE (⟨41, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨41, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨41, by omega⟩ : Fin 1104)).2.2 = 21076692611 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_42 :
    ((certNum ⟨42, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨42, by omega⟩) ⟨42, by omega⟩ (certE ⟨42, by omega⟩) := by
  have hm : certMode (⟨42, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨42, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨42, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨42, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨42, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_43 :
    ((certNum ⟨43, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨43, by omega⟩) ⟨43, by omega⟩ (certE ⟨43, by omega⟩) := by
  have hm : certMode (⟨43, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨43, by omega⟩ : Fin 1104) = 203948434383294623632018014076 := by decide +kernel
  have he : certE (⟨43, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨43, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨43, by omega⟩ : Fin 1104)).2.2 = 21076900065 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_44 :
    ((certNum ⟨44, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨44, by omega⟩) ⟨44, by omega⟩ (certE ⟨44, by omega⟩) := by
  have hm : certMode (⟨44, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨44, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨44, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨44, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨44, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_45 :
    ((certNum ⟨45, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨45, by omega⟩) ⟨45, by omega⟩ (certE ⟨45, by omega⟩) := by
  have hm : certMode (⟨45, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨45, by omega⟩ : Fin 1104) = 203946431285118076245582371335 := by decide +kernel
  have he : certE (⟨45, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨45, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨45, by omega⟩ : Fin 1104)).2.2 = 21076637632 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_46 :
    ((certNum ⟨46, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨46, by omega⟩) ⟨46, by omega⟩ (certE ⟨46, by omega⟩) := by
  have hm : certMode (⟨46, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨46, by omega⟩ : Fin 1104) = 23257825681277212885890399437 := by decide +kernel
  have he : certE (⟨46, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (37 : Int) else if j.val = 1 then -1 else if j.val = 2 then -8 else -6) else (if j.val = 0 then -23 else if j.val = 1 then -2 else if j.val = 2 then 0 else 6)) := by decide +kernel
  have hp : parent2 (⟨46, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨46, by omega⟩ : Fin 1104)).2.2 = 1558291252 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_47 :
    ((certNum ⟨47, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨47, by omega⟩) ⟨47, by omega⟩ (certE ⟨47, by omega⟩) := by
  have hm : certMode (⟨47, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨47, by omega⟩ : Fin 1104) = 203971932003227322645729715039 := by decide +kernel
  have he : certE (⟨47, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 1 else if j.val = 1 then -2 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hp : parent2 (⟨47, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨47, by omega⟩ : Fin 1104)).2.2 = 21079978622 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_48 :
    ((certNum ⟨48, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨48, by omega⟩) ⟨48, by omega⟩ (certE ⟨48, by omega⟩) := by
  have hm : certMode (⟨48, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨48, by omega⟩ : Fin 1104) = 203945851899747311132346203712 := by decide +kernel
  have he : certE (⟨48, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨48, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨48, by omega⟩ : Fin 1104)).2.2 = 21076561725 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_49 :
    ((certNum ⟨49, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨49, by omega⟩) ⟨49, by omega⟩ (certE ⟨49, by omega⟩) := by
  have hm : certMode (⟨49, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨49, by omega⟩ : Fin 1104) = 154725203961522851911135307020 := by decide +kernel
  have he : certE (⟨49, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -24 else if j.val = 1 then 6 else if j.val = 2 then 0 else 3)) := by decide +kernel
  have hp : parent2 (⟨49, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨49, by omega⟩ : Fin 1104)).2.2 = 14902773193 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_50 :
    ((certNum ⟨50, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨50, by omega⟩) ⟨50, by omega⟩ (certE ⟨50, by omega⟩) := by
  have hm : certMode (⟨50, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨50, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨50, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨50, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨50, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_51 :
    ((certNum ⟨51, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨51, by omega⟩) ⟨51, by omega⟩ (certE ⟨51, by omega⟩) := by
  have hm : certMode (⟨51, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨51, by omega⟩ : Fin 1104) = 203945433879366684494352329518 := by decide +kernel
  have he : certE (⟨51, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨51, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨51, by omega⟩ : Fin 1104)).2.2 = 21076506959 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_52 :
    ((certNum ⟨52, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨52, by omega⟩) ⟨52, by omega⟩ (certE ⟨52, by omega⟩) := by
  have hm : certMode (⟨52, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨52, by omega⟩ : Fin 1104) = 23257057920720071775253587703 := by decide +kernel
  have he : certE (⟨52, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (37 : Int) else if j.val = 1 then -1 else if j.val = 2 then -8 else -6) else (if j.val = 0 then -23 else if j.val = 1 then -2 else if j.val = 2 then 0 else 6)) := by decide +kernel
  have hp : parent2 (⟨52, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨52, by omega⟩ : Fin 1104)).2.2 = 1558231838 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_53 :
    ((certNum ⟨53, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨53, by omega⟩) ⟨53, by omega⟩ (certE ⟨53, by omega⟩) := by
  have hm : certMode (⟨53, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨53, by omega⟩ : Fin 1104) = 203879282569644665645076853913 := by decide +kernel
  have he : certE (⟨53, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨53, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨53, by omega⟩ : Fin 1104)).2.2 = 21067840867 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_54 :
    ((certNum ⟨54, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨54, by omega⟩) ⟨54, by omega⟩ (certE ⟨54, by omega⟩) := by
  have hm : certMode (⟨54, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨54, by omega⟩ : Fin 1104) = 204038687635425124848446129814 := by decide +kernel
  have he : certE (⟨54, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨54, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨54, by omega⟩ : Fin 1104)).2.2 = 21088725348 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_55 :
    ((certNum ⟨55, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨55, by omega⟩) ⟨55, by omega⟩ (certE ⟨55, by omega⟩) := by
  have hm : certMode (⟨55, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨55, by omega⟩ : Fin 1104) = 154744050097580653334712125208 := by decide +kernel
  have he : certE (⟨55, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then 27 else if j.val = 1 then -7 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨55, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨55, by omega⟩ : Fin 1104)).2.2 = 14905029788 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_56 :
    ((certNum ⟨56, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨56, by omega⟩) ⟨56, by omega⟩ (certE ⟨56, by omega⟩) := by
  have hm : certMode (⟨56, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨56, by omega⟩ : Fin 1104) = 203878787378446887597017068870 := by decide +kernel
  have he : certE (⟨56, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨56, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨56, by omega⟩ : Fin 1104)).2.2 = 21067775997 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_57 :
    ((certNum ⟨57, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨57, by omega⟩) ⟨57, by omega⟩ (certE ⟨57, by omega⟩) := by
  have hm : certMode (⟨57, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨57, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨57, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨57, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨57, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_58 :
    ((certNum ⟨58, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨58, by omega⟩) ⟨58, by omega⟩ (certE ⟨58, by omega⟩) := by
  have hm : certMode (⟨58, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨58, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨58, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨58, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨58, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_59 :
    ((certNum ⟨59, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨59, by omega⟩) ⟨59, by omega⟩ (certE ⟨59, by omega⟩) := by
  have hm : certMode (⟨59, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨59, by omega⟩ : Fin 1104) = 203309859589816843181817454750 := by decide +kernel
  have he : certE (⟨59, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨59, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨59, by omega⟩ : Fin 1104)).2.2 = 20993285936 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_60 :
    ((certNum ⟨60, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨60, by omega⟩) ⟨60, by omega⟩ (certE ⟨60, by omega⟩) := by
  have hm : certMode (⟨60, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨60, by omega⟩ : Fin 1104) = 190861710447275474782245112783 := by decide +kernel
  have he : certE (⟨60, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hp : parent2 (⟨60, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨60, by omega⟩ : Fin 1104)).2.2 = 19381560954 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_61 :
    ((certNum ⟨61, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨61, by omega⟩) ⟨61, by omega⟩ (certE ⟨61, by omega⟩) := by
  have hm : certMode (⟨61, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨61, by omega⟩ : Fin 1104) = 89380306009678530820400553917 := by decide +kernel
  have he : certE (⟨61, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 8 else if j.val = 1 then 7 else if j.val = 2 then -4 else -6)) := by decide +kernel
  have hp : parent2 (⟨61, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨61, by omega⟩ : Fin 1104)).2.2 = 7612993848 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_62 :
    ((certNum ⟨62, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨62, by omega⟩) ⟨62, by omega⟩ (certE ⟨62, by omega⟩) := by
  have hm : certMode (⟨62, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨62, by omega⟩ : Fin 1104) = 203309867391962858906385030705 := by decide +kernel
  have he : certE (⟨62, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -2 else if j.val = 1 then 8 else if j.val = 2 then -7 else 0)) := by decide +kernel
  have hp : parent2 (⟨62, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨62, by omega⟩ : Fin 1104)).2.2 = 20993286957 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_63 :
    ((certNum ⟨63, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨63, by omega⟩) ⟨63, by omega⟩ (certE ⟨63, by omega⟩) := by
  have hm : certMode (⟨63, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨63, by omega⟩ : Fin 1104) = 181576608960190319049121094719 := by decide +kernel
  have he : certE (⟨63, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 13 else if j.val = 1 then -8 else if j.val = 2 then 1 else -3)) := by decide +kernel
  have hp : parent2 (⟨63, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨63, by omega⟩ : Fin 1104)).2.2 = 18202107551 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_64 :
    ((certNum ⟨64, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨64, by omega⟩) ⟨64, by omega⟩ (certE ⟨64, by omega⟩) := by
  have hm : certMode (⟨64, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨64, by omega⟩ : Fin 1104) = 202779412172501819280209495672 := by decide +kernel
  have he : certE (⟨64, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨64, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨64, by omega⟩ : Fin 1104)).2.2 = 20923898598 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_65 :
    ((certNum ⟨65, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨65, by omega⟩) ⟨65, by omega⟩ (certE ⟨65, by omega⟩) := by
  have hm : certMode (⟨65, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨65, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨65, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨65, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨65, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_66 :
    ((certNum ⟨66, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨66, by omega⟩) ⟨66, by omega⟩ (certE ⟨66, by omega⟩) := by
  have hm : certMode (⟨66, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨66, by omega⟩ : Fin 1104) = 190817948791701041389281763847 := by decide +kernel
  have he : certE (⟨66, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨66, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨66, by omega⟩ : Fin 1104)).2.2 = 19375956243 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_67 :
    ((certNum ⟨67, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨67, by omega⟩) ⟨67, by omega⟩ (certE ⟨67, by omega⟩) := by
  have hm : certMode (⟨67, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨67, by omega⟩ : Fin 1104) = 202779404990882600914620489357 := by decide +kernel
  have he : certE (⟨67, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨67, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨67, by omega⟩ : Fin 1104)).2.2 = 20923897659 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_68 :
    ((certNum ⟨68, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨68, by omega⟩) ⟨68, by omega⟩ (certE ⟨68, by omega⟩) := by
  have hm : certMode (⟨68, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨68, by omega⟩ : Fin 1104) = 90567253922254609909714415542 := by decide +kernel
  have he : certE (⟨68, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then -34 else if j.val = 1 then 5 else if j.val = 2 then 7 else 1)) := by decide +kernel
  have hp : parent2 (⟨68, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨68, by omega⟩ : Fin 1104)).2.2 = 7735247595 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_69 :
    ((certNum ⟨69, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨69, by omega⟩) ⟨69, by omega⟩ (certE ⟨69, by omega⟩) := by
  have hm : certMode (⟨69, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨69, by omega⟩ : Fin 1104) = 181353210128158541352794081713 := by decide +kernel
  have he : certE (⟨69, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then -18 else if j.val = 1 then -2 else if j.val = 2 then 3 else 3)) := by decide +kernel
  have hp : parent2 (⟨69, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨69, by omega⟩ : Fin 1104)).2.2 = 18173971401 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_70 :
    ((certNum ⟨70, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨70, by omega⟩) ⟨70, by omega⟩ (certE ⟨70, by omega⟩) := by
  have hm : certMode (⟨70, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨70, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨70, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨70, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨70, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_71 :
    ((certNum ⟨71, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨71, by omega⟩) ⟨71, by omega⟩ (certE ⟨71, by omega⟩) := by
  have hm : certMode (⟨71, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨71, by omega⟩ : Fin 1104) = 169478992461395180174747618461 := by decide +kernel
  have he : certE (⟨71, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then -23 else if j.val = 1 then -1 else if j.val = 2 then 2 else 5)) := by decide +kernel
  have hp : parent2 (⟨71, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨71, by omega⟩ : Fin 1104)).2.2 = 16694913619 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_72 :
    ((certNum ⟨72, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨72, by omega⟩) ⟨72, by omega⟩ (certE ⟨72, by omega⟩) := by
  have hm : certMode (⟨72, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨72, by omega⟩ : Fin 1104) = 203945802576334864587897753630 := by decide +kernel
  have he : certE (⟨72, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨72, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨72, by omega⟩ : Fin 1104)).2.2 = 21076555263 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_73 :
    ((certNum ⟨73, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨73, by omega⟩) ⟨73, by omega⟩ (certE ⟨73, by omega⟩) := by
  have hm : certMode (⟨73, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨73, by omega⟩ : Fin 1104) = 203875567943563965353133316271 := by decide +kernel
  have he : certE (⟨73, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨73, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨73, by omega⟩ : Fin 1104)).2.2 = 21067354254 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_74 :
    ((certNum ⟨74, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨74, by omega⟩) ⟨74, by omega⟩ (certE ⟨74, by omega⟩) := by
  have hm : certMode (⟨74, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨74, by omega⟩ : Fin 1104) = 53036191349728546831146676424 := by decide +kernel
  have he : certE (⟨74, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then -1 else -2)) := by decide +kernel
  have hp : parent2 (⟨74, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨74, by omega⟩ : Fin 1104)).2.2 = 4081460277 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_75 :
    ((certNum ⟨75, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨75, by omega⟩) ⟨75, by omega⟩ (certE ⟨75, by omega⟩) := by
  have hm : certMode (⟨75, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨75, by omega⟩ : Fin 1104) = 203945832290982196216514597981 := by decide +kernel
  have he : certE (⟨75, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨75, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨75, by omega⟩ : Fin 1104)).2.2 = 21076559156 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_76 :
    ((certNum ⟨76, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨76, by omega⟩) ⟨76, by omega⟩ (certE ⟨76, by omega⟩) := by
  have hm : certMode (⟨76, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨76, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨76, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨76, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨76, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_77 :
    ((certNum ⟨77, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨77, by omega⟩) ⟨77, by omega⟩ (certE ⟨77, by omega⟩) := by
  have hm : certMode (⟨77, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨77, by omega⟩ : Fin 1104) = 196593332716462679163552993941 := by decide +kernel
  have he : certE (⟨77, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then 25 else if j.val = 1 then -4 else if j.val = 2 then -2 else -7)) := by decide +kernel
  have hp : parent2 (⟨77, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨77, by omega⟩ : Fin 1104)).2.2 = 20119347778 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_78 :
    ((certNum ⟨78, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨78, by omega⟩) ⟨78, by omega⟩ (certE ⟨78, by omega⟩) := by
  have hm : certMode (⟨78, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨78, by omega⟩ : Fin 1104) = 4118393106217115489267310 := by decide +kernel
  have he : certE (⟨78, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -27 else if j.val = 1 then -1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hp : parent2 (⟨78, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨78, by omega⟩ : Fin 1104)).2.2 = 121689 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_79 :
    ((certNum ⟨79, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨79, by omega⟩) ⟨79, by omega⟩ (certE ⟨79, by omega⟩) := by
  have hm : certMode (⟨79, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨79, by omega⟩ : Fin 1104) = 3980162916589866558861570 := by decide +kernel
  have he : certE (⟨79, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 0 else 1)) := by decide +kernel
  have hp : parent2 (⟨79, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨79, by omega⟩ : Fin 1104)).2.2 = 117353 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_80 :
    ((certNum ⟨80, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨80, by omega⟩) ⟨80, by omega⟩ (certE ⟨80, by omega⟩) := by
  have hm : certMode (⟨80, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨80, by omega⟩ : Fin 1104) = 196593331116336342926920661468 := by decide +kernel
  have he : certE (⟨80, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then 25 else if j.val = 1 then -4 else if j.val = 2 then -2 else -7)) := by decide +kernel
  have hp : parent2 (⟨80, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨80, by omega⟩ : Fin 1104)).2.2 = 20119347571 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_81 :
    ((certNum ⟨81, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨81, by omega⟩) ⟨81, by omega⟩ (certE ⟨81, by omega⟩) := by
  have hm : certMode (⟨81, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨81, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨81, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨81, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨81, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_82 :
    ((certNum ⟨82, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨82, by omega⟩) ⟨82, by omega⟩ (certE ⟨82, by omega⟩) := by
  have hm : certMode (⟨82, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨82, by omega⟩ : Fin 1104) = 203783301125382148734646076115 := by decide +kernel
  have he : certE (⟨82, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨82, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨82, by omega⟩ : Fin 1104)).2.2 = 21055268660 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_83 :
    ((certNum ⟨83, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨83, by omega⟩) ⟨83, by omega⟩ (certE ⟨83, by omega⟩) := by
  have hm : certMode (⟨83, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨83, by omega⟩ : Fin 1104) = 53034220129152041035495468900 := by decide +kernel
  have he : certE (⟨83, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then -1 else -2)) := by decide +kernel
  have hp : parent2 (⟨83, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨83, by omega⟩ : Fin 1104)).2.2 = 4081280853 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_84 :
    ((certNum ⟨84, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨84, by omega⟩) ⟨84, by omega⟩ (certE ⟨84, by omega⟩) := by
  have hm : certMode (⟨84, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨84, by omega⟩ : Fin 1104) = 204038730884381373402679432890 := by decide +kernel
  have he : certE (⟨84, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨84, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨84, by omega⟩ : Fin 1104)).2.2 = 21088731015 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_85 :
    ((certNum ⟨85, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨85, by omega⟩) ⟨85, by omega⟩ (certE ⟨85, by omega⟩) := by
  have hm : certMode (⟨85, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨85, by omega⟩ : Fin 1104) = 203783240822729800447833748217 := by decide +kernel
  have he : certE (⟨85, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨85, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨85, by omega⟩ : Fin 1104)).2.2 = 21055260762 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_86 :
    ((certNum ⟨86, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨86, by omega⟩) ⟨86, by omega⟩ (certE ⟨86, by omega⟩) := by
  have hm : certMode (⟨86, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨86, by omega⟩ : Fin 1104) = 169524341723380188158434282687 := by decide +kernel
  have he : certE (⟨86, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then -24 else if j.val = 1 then -8 else if j.val = 2 then 6 else 6)) := by decide +kernel
  have hp : parent2 (⟨86, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨86, by omega⟩ : Fin 1104)).2.2 = 16700500508 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_87 :
    ((certNum ⟨87, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨87, by omega⟩) ⟨87, by omega⟩ (certE ⟨87, by omega⟩) := by
  have hm : certMode (⟨87, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨87, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨87, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨87, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨87, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_88 :
    ((certNum ⟨88, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨88, by omega⟩) ⟨88, by omega⟩ (certE ⟨88, by omega⟩) := by
  have hm : certMode (⟨88, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨88, by omega⟩ : Fin 1104) = 168696720857282220658582032 := by decide +kernel
  have he : certE (⟨88, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -26 else if j.val = 1 then 7 else if j.val = 2 then -1 else 0)) := by decide +kernel
  have hp : parent2 (⟨88, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨88, by omega⟩ : Fin 1104)).2.2 = 6517948 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_89 :
    ((certNum ⟨89, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨89, by omega⟩) ⟨89, by omega⟩ (certE ⟨89, by omega⟩) := by
  have hm : certMode (⟨89, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨89, by omega⟩ : Fin 1104) = 203948603349928210764637700728 := by decide +kernel
  have he : certE (⟨89, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨89, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨89, by omega⟩ : Fin 1104)).2.2 = 21076922202 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_90 :
    ((certNum ⟨90, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨90, by omega⟩) ⟨90, by omega⟩ (certE ⟨90, by omega⟩) := by
  have hm : certMode (⟨90, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨90, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨90, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨90, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨90, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_91 :
    ((certNum ⟨91, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨91, by omega⟩) ⟨91, by omega⟩ (certE ⟨91, by omega⟩) := by
  have hm : certMode (⟨91, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨91, by omega⟩ : Fin 1104) = 203947106331331039496077867248 := by decide +kernel
  have he : certE (⟨91, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨91, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨91, by omega⟩ : Fin 1104)).2.2 = 21076726072 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨0 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨0 + j.val, by omega⟩) ⟨0 + j.val, by omega⟩
        (certE ⟨0 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_0
  | ⟨1, _⟩ => exact MME.L2Cert.cert_1
  | ⟨2, _⟩ => exact MME.L2Cert.cert_2
  | ⟨3, _⟩ => exact MME.L2Cert.cert_3
  | ⟨4, _⟩ => exact MME.L2Cert.cert_4
  | ⟨5, _⟩ => exact MME.L2Cert.cert_5
  | ⟨6, _⟩ => exact MME.L2Cert.cert_6
  | ⟨7, _⟩ => exact MME.L2Cert.cert_7
  | ⟨8, _⟩ => exact MME.L2Cert.cert_8
  | ⟨9, _⟩ => exact MME.L2Cert.cert_9
  | ⟨10, _⟩ => exact MME.L2Cert.cert_10
  | ⟨11, _⟩ => exact MME.L2Cert.cert_11
  | ⟨12, _⟩ => exact MME.L2Cert.cert_12
  | ⟨13, _⟩ => exact MME.L2Cert.cert_13
  | ⟨14, _⟩ => exact MME.L2Cert.cert_14
  | ⟨15, _⟩ => exact MME.L2Cert.cert_15
  | ⟨16, _⟩ => exact MME.L2Cert.cert_16
  | ⟨17, _⟩ => exact MME.L2Cert.cert_17
  | ⟨18, _⟩ => exact MME.L2Cert.cert_18
  | ⟨19, _⟩ => exact MME.L2Cert.cert_19
  | ⟨20, _⟩ => exact MME.L2Cert.cert_20
  | ⟨21, _⟩ => exact MME.L2Cert.cert_21
  | ⟨22, _⟩ => exact MME.L2Cert.cert_22
  | ⟨23, _⟩ => exact MME.L2Cert.cert_23
  | ⟨24, _⟩ => exact MME.L2Cert.cert_24
  | ⟨25, _⟩ => exact MME.L2Cert.cert_25
  | ⟨26, _⟩ => exact MME.L2Cert.cert_26
  | ⟨27, _⟩ => exact MME.L2Cert.cert_27
  | ⟨28, _⟩ => exact MME.L2Cert.cert_28
  | ⟨29, _⟩ => exact MME.L2Cert.cert_29
  | ⟨30, _⟩ => exact MME.L2Cert.cert_30
  | ⟨31, _⟩ => exact MME.L2Cert.cert_31
  | ⟨32, _⟩ => exact MME.L2Cert.cert_32
  | ⟨33, _⟩ => exact MME.L2Cert.cert_33
  | ⟨34, _⟩ => exact MME.L2Cert.cert_34
  | ⟨35, _⟩ => exact MME.L2Cert.cert_35
  | ⟨36, _⟩ => exact MME.L2Cert.cert_36
  | ⟨37, _⟩ => exact MME.L2Cert.cert_37
  | ⟨38, _⟩ => exact MME.L2Cert.cert_38
  | ⟨39, _⟩ => exact MME.L2Cert.cert_39
  | ⟨40, _⟩ => exact MME.L2Cert.cert_40
  | ⟨41, _⟩ => exact MME.L2Cert.cert_41
  | ⟨42, _⟩ => exact MME.L2Cert.cert_42
  | ⟨43, _⟩ => exact MME.L2Cert.cert_43
  | ⟨44, _⟩ => exact MME.L2Cert.cert_44
  | ⟨45, _⟩ => exact MME.L2Cert.cert_45
  | ⟨46, _⟩ => exact MME.L2Cert.cert_46
  | ⟨47, _⟩ => exact MME.L2Cert.cert_47
  | ⟨48, _⟩ => exact MME.L2Cert.cert_48
  | ⟨49, _⟩ => exact MME.L2Cert.cert_49
  | ⟨50, _⟩ => exact MME.L2Cert.cert_50
  | ⟨51, _⟩ => exact MME.L2Cert.cert_51
  | ⟨52, _⟩ => exact MME.L2Cert.cert_52
  | ⟨53, _⟩ => exact MME.L2Cert.cert_53
  | ⟨54, _⟩ => exact MME.L2Cert.cert_54
  | ⟨55, _⟩ => exact MME.L2Cert.cert_55
  | ⟨56, _⟩ => exact MME.L2Cert.cert_56
  | ⟨57, _⟩ => exact MME.L2Cert.cert_57
  | ⟨58, _⟩ => exact MME.L2Cert.cert_58
  | ⟨59, _⟩ => exact MME.L2Cert.cert_59
  | ⟨60, _⟩ => exact MME.L2Cert.cert_60
  | ⟨61, _⟩ => exact MME.L2Cert.cert_61
  | ⟨62, _⟩ => exact MME.L2Cert.cert_62
  | ⟨63, _⟩ => exact MME.L2Cert.cert_63
  | ⟨64, _⟩ => exact MME.L2Cert.cert_64
  | ⟨65, _⟩ => exact MME.L2Cert.cert_65
  | ⟨66, _⟩ => exact MME.L2Cert.cert_66
  | ⟨67, _⟩ => exact MME.L2Cert.cert_67
  | ⟨68, _⟩ => exact MME.L2Cert.cert_68
  | ⟨69, _⟩ => exact MME.L2Cert.cert_69
  | ⟨70, _⟩ => exact MME.L2Cert.cert_70
  | ⟨71, _⟩ => exact MME.L2Cert.cert_71
  | ⟨72, _⟩ => exact MME.L2Cert.cert_72
  | ⟨73, _⟩ => exact MME.L2Cert.cert_73
  | ⟨74, _⟩ => exact MME.L2Cert.cert_74
  | ⟨75, _⟩ => exact MME.L2Cert.cert_75
  | ⟨76, _⟩ => exact MME.L2Cert.cert_76
  | ⟨77, _⟩ => exact MME.L2Cert.cert_77
  | ⟨78, _⟩ => exact MME.L2Cert.cert_78
  | ⟨79, _⟩ => exact MME.L2Cert.cert_79
  | ⟨80, _⟩ => exact MME.L2Cert.cert_80
  | ⟨81, _⟩ => exact MME.L2Cert.cert_81
  | ⟨82, _⟩ => exact MME.L2Cert.cert_82
  | ⟨83, _⟩ => exact MME.L2Cert.cert_83
  | ⟨84, _⟩ => exact MME.L2Cert.cert_84
  | ⟨85, _⟩ => exact MME.L2Cert.cert_85
  | ⟨86, _⟩ => exact MME.L2Cert.cert_86
  | ⟨87, _⟩ => exact MME.L2Cert.cert_87
  | ⟨88, _⟩ => exact MME.L2Cert.cert_88
  | ⟨89, _⟩ => exact MME.L2Cert.cert_89
  | ⟨90, _⟩ => exact MME.L2Cert.cert_90
  | ⟨91, _⟩ => exact MME.L2Cert.cert_91
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
