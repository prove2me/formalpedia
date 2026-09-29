-- Prove2me | solution 1 for mme_released_recursive_level2_cert2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:04:45.019641+00:00
-- url     : https://prove2.me/submissions/a9fb88a6-517e-49e0-9e81-66c3d9e4ec44

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

theorem cert_184 :
    ((certNum ⟨184, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨184, by omega⟩) ⟨184, by omega⟩ (certE ⟨184, by omega⟩) := by
  have hm : certMode (⟨184, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨184, by omega⟩ : Fin 1104) = 179757996479218093008860545517 := by decide +kernel
  have he : certE (⟨184, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -2 else -4)) := by decide +kernel
  have hp : parent2 (⟨184, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨184, by omega⟩ : Fin 1104)).2.2 = 17973390621 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_185 :
    ((certNum ⟨185, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨185, by omega⟩) ⟨185, by omega⟩ (certE ⟨185, by omega⟩) := by
  have hm : certMode (⟨185, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨185, by omega⟩ : Fin 1104) = 179757262339741581791351419206 := by decide +kernel
  have he : certE (⟨185, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -2 else -4)) := by decide +kernel
  have hp : parent2 (⟨185, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨185, by omega⟩ : Fin 1104)).2.2 = 17973298442 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_186 :
    ((certNum ⟨186, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨186, by omega⟩) ⟨186, by omega⟩ (certE ⟨186, by omega⟩) := by
  have hm : certMode (⟨186, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨186, by omega⟩ : Fin 1104) = 179757997450859099266986762523 := by decide +kernel
  have he : certE (⟨186, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -2 else -4)) := by decide +kernel
  have hp : parent2 (⟨186, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨186, by omega⟩ : Fin 1104)).2.2 = 17973390743 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_187 :
    ((certNum ⟨187, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨187, by omega⟩) ⟨187, by omega⟩ (certE ⟨187, by omega⟩) := by
  have hm : certMode (⟨187, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨187, by omega⟩ : Fin 1104) = 179757086480157226473627733815 := by decide +kernel
  have he : certE (⟨187, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -2 else -4)) := by decide +kernel
  have hp : parent2 (⟨187, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨187, by omega⟩ : Fin 1104)).2.2 = 17973276361 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_188 :
    ((certNum ⟨188, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨188, by omega⟩) ⟨188, by omega⟩ (certE ⟨188, by omega⟩) := by
  have hm : certMode (⟨188, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨188, by omega⟩ : Fin 1104) = 179756691952496664406636259515 := by decide +kernel
  have he : certE (⟨188, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -2 else -4)) := by decide +kernel
  have hp : parent2 (⟨188, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨188, by omega⟩ : Fin 1104)).2.2 = 17973226824 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_189 :
    ((certNum ⟨189, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨189, by omega⟩) ⟨189, by omega⟩ (certE ⟨189, by omega⟩) := by
  have hm : certMode (⟨189, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨189, by omega⟩ : Fin 1104) = 179756690765814714421421629369 := by decide +kernel
  have he : certE (⟨189, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -2 else -4)) := by decide +kernel
  have hp : parent2 (⟨189, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨189, by omega⟩ : Fin 1104)).2.2 = 17973226675 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_190 :
    ((certNum ⟨190, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨190, by omega⟩) ⟨190, by omega⟩ (certE ⟨190, by omega⟩) := by
  have hm : certMode (⟨190, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨190, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨190, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨190, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨190, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_191 :
    ((certNum ⟨191, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨191, by omega⟩) ⟨191, by omega⟩ (certE ⟨191, by omega⟩) := by
  have hm : certMode (⟨191, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨191, by omega⟩ : Fin 1104) = 203773425973142046759769092455 := by decide +kernel
  have he : certE (⟨191, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨191, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨191, by omega⟩ : Fin 1104)).2.2 = 21053975286 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_192 :
    ((certNum ⟨192, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨192, by omega⟩) ⟨192, by omega⟩ (certE ⟨192, by omega⟩) := by
  have hm : certMode (⟨192, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨192, by omega⟩ : Fin 1104) = 180601532956382285094413674171 := by decide +kernel
  have he : certE (⟨192, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨192, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨192, by omega⟩ : Fin 1104)).2.2 = 18079383755 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_193 :
    ((certNum ⟨193, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨193, by omega⟩) ⟨193, by omega⟩ (certE ⟨193, by omega⟩) := by
  have hm : certMode (⟨193, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨193, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨193, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨193, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨193, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_194 :
    ((certNum ⟨194, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨194, by omega⟩) ⟨194, by omega⟩ (certE ⟨194, by omega⟩) := by
  have hm : certMode (⟨194, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨194, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨194, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨194, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨194, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_195 :
    ((certNum ⟨195, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨195, by omega⟩) ⟨195, by omega⟩ (certE ⟨195, by omega⟩) := by
  have hm : certMode (⟨195, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨195, by omega⟩ : Fin 1104) = 203773079768784043557839224032 := by decide +kernel
  have he : certE (⟨195, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨195, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨195, by omega⟩ : Fin 1104)).2.2 = 21053929942 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_196 :
    ((certNum ⟨196, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨196, by omega⟩) ⟨196, by omega⟩ (certE ⟨196, by omega⟩) := by
  have hm : certMode (⟨196, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨196, by omega⟩ : Fin 1104) = 157530682010676704404500084 := by decide +kernel
  have he : certE (⟨196, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -10 else if j.val = 1 then -5 else if j.val = 2 then -7 else 6)) := by decide +kernel
  have hp : parent2 (⟨196, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨196, by omega⟩ : Fin 1104)).2.2 = 6051825 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_197 :
    ((certNum ⟨197, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨197, by omega⟩) ⟨197, by omega⟩ (certE ⟨197, by omega⟩) := by
  have hm : certMode (⟨197, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨197, by omega⟩ : Fin 1104) = 203771949173249172160934408733 := by decide +kernel
  have he : certE (⟨197, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨197, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨197, by omega⟩ : Fin 1104)).2.2 = 21053781863 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_198 :
    ((certNum ⟨198, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨198, by omega⟩) ⟨198, by omega⟩ (certE ⟨198, by omega⟩) := by
  have hm : certMode (⟨198, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨198, by omega⟩ : Fin 1104) = 180607114407803593023448004461 := by decide +kernel
  have he : certE (⟨198, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨198, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨198, by omega⟩ : Fin 1104)).2.2 = 18080085626 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_199 :
    ((certNum ⟨199, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨199, by omega⟩) ⟨199, by omega⟩ (certE ⟨199, by omega⟩) := by
  have hm : certMode (⟨199, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨199, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨199, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨199, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨199, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_200 :
    ((certNum ⟨200, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨200, by omega⟩) ⟨200, by omega⟩ (certE ⟨200, by omega⟩) := by
  have hm : certMode (⟨200, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨200, by omega⟩ : Fin 1104) = 10617089159978429396648610790 := by decide +kernel
  have he : certE (⟨200, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 0 else if j.val = 1 then -2 else if j.val = 2 then -2 else -1)) := by decide +kernel
  have hp : parent2 (⟨200, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨200, by omega⟩ : Fin 1104)).2.2 = 634884705 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_201 :
    ((certNum ⟨201, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨201, by omega⟩) ⟨201, by omega⟩ (certE ⟨201, by omega⟩) := by
  have hm : certMode (⟨201, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨201, by omega⟩ : Fin 1104) = 202779684278494195473571255173 := by decide +kernel
  have he : certE (⟨201, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨201, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨201, by omega⟩ : Fin 1104)).2.2 = 20923934176 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_202 :
    ((certNum ⟨202, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨202, by omega⟩) ⟨202, by omega⟩ (certE ⟨202, by omega⟩) := by
  have hm : certMode (⟨202, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨202, by omega⟩ : Fin 1104) = 10617288801894447404100739937 := by decide +kernel
  have he : certE (⟨202, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 0 else if j.val = 1 then -2 else if j.val = 2 then -2 else -1)) := by decide +kernel
  have hp : parent2 (⟨202, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨202, by omega⟩ : Fin 1104)).2.2 = 634898266 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_203 :
    ((certNum ⟨203, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨203, by omega⟩) ⟨203, by omega⟩ (certE ⟨203, by omega⟩) := by
  have hm : certMode (⟨203, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨203, by omega⟩ : Fin 1104) = 202779931321269992227316100634 := by decide +kernel
  have he : certE (⟨203, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨203, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨203, by omega⟩ : Fin 1104)).2.2 = 20923966477 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_204 :
    ((certNum ⟨204, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨204, by omega⟩) ⟨204, by omega⟩ (certE ⟨204, by omega⟩) := by
  have hm : certMode (⟨204, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨204, by omega⟩ : Fin 1104) = 18682809877547717784899059637 := by decide +kernel
  have he : certE (⟨204, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -12 else if j.val = 1 then 5 else if j.val = 2 then 0 else -2)) := by decide +kernel
  have hp : parent2 (⟨204, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨204, by omega⟩ : Fin 1104)).2.2 = 1210765125 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_205 :
    ((certNum ⟨205, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨205, by omega⟩) ⟨205, by omega⟩ (certE ⟨205, by omega⟩) := by
  have hm : certMode (⟨205, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨205, by omega⟩ : Fin 1104) = 202779574428101061135344430631 := by decide +kernel
  have he : certE (⟨205, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨205, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨205, by omega⟩ : Fin 1104)).2.2 = 20923919813 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_206 :
    ((certNum ⟨206, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨206, by omega⟩) ⟨206, by omega⟩ (certE ⟨206, by omega⟩) := by
  have hm : certMode (⟨206, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨206, by omega⟩ : Fin 1104) = 203305744793012317408176570198 := by decide +kernel
  have he : certE (⟨206, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨206, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨206, by omega⟩ : Fin 1104)).2.2 = 20992747448 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_207 :
    ((certNum ⟨207, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨207, by omega⟩) ⟨207, by omega⟩ (certE ⟨207, by omega⟩) := by
  have hm : certMode (⟨207, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨207, by omega⟩ : Fin 1104) = 5072574295690850391317439191 := by decide +kernel
  have he : certE (⟨207, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -16 else if j.val = 1 then -2 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨207, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨207, by omega⟩ : Fin 1104)).2.2 = 275818638 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_208 :
    ((certNum ⟨208, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨208, by omega⟩) ⟨208, by omega⟩ (certE ⟨208, by omega⟩) := by
  have hm : certMode (⟨208, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨208, by omega⟩ : Fin 1104) = 203305457139928098015914020622 := by decide +kernel
  have he : certE (⟨208, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨208, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨208, by omega⟩ : Fin 1104)).2.2 = 20992709804 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_209 :
    ((certNum ⟨209, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨209, by omega⟩) ⟨209, by omega⟩ (certE ⟨209, by omega⟩) := by
  have hm : certMode (⟨209, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨209, by omega⟩ : Fin 1104) = 5072554872827579515058575642 := by decide +kernel
  have he : certE (⟨209, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -15 else if j.val = 1 then -6 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hp : parent2 (⟨209, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨209, by omega⟩ : Fin 1104)).2.2 = 275817453 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_210 :
    ((certNum ⟨210, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨210, by omega⟩) ⟨210, by omega⟩ (certE ⟨210, by omega⟩) := by
  have hm : certMode (⟨210, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨210, by omega⟩ : Fin 1104) = 203305787111094484591159446080 := by decide +kernel
  have he : certE (⟨210, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨210, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨210, by omega⟩ : Fin 1104)).2.2 = 20992752986 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_211 :
    ((certNum ⟨211, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨211, by omega⟩) ⟨211, by omega⟩ (certE ⟨211, by omega⟩) := by
  have hm : certMode (⟨211, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨211, by omega⟩ : Fin 1104) = 10588670115020811684465233734 := by decide +kernel
  have he : certE (⟨211, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -11 else if j.val = 1 then -3 else if j.val = 2 then 1 else 1)) := by decide +kernel
  have hp : parent2 (⟨211, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨211, by omega⟩ : Fin 1104)).2.2 = 632954686 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_212 :
    ((certNum ⟨212, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨212, by omega⟩) ⟨212, by omega⟩ (certE ⟨212, by omega⟩) := by
  have hm : certMode (⟨212, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨212, by omega⟩ : Fin 1104) = 203878266903888922971787608728 := by decide +kernel
  have he : certE (⟨212, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨212, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨212, by omega⟩ : Fin 1104)).2.2 = 21067707815 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_213 :
    ((certNum ⟨213, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨213, by omega⟩) ⟨213, by omega⟩ (certE ⟨213, by omega⟩) := by
  have hm : certMode (⟨213, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨213, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨213, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨213, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨213, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_214 :
    ((certNum ⟨214, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨214, by omega⟩) ⟨214, by omega⟩ (certE ⟨214, by omega⟩) := by
  have hm : certMode (⟨214, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨214, by omega⟩ : Fin 1104) = 203877846123558099880993137504 := by decide +kernel
  have he : certE (⟨214, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨214, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨214, by omega⟩ : Fin 1104)).2.2 = 21067652693 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_215 :
    ((certNum ⟨215, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨215, by omega⟩) ⟨215, by omega⟩ (certE ⟨215, by omega⟩) := by
  have hm : certMode (⟨215, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨215, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨215, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨215, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨215, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_216 :
    ((certNum ⟨216, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨216, by omega⟩) ⟨216, by omega⟩ (certE ⟨216, by omega⟩) := by
  have hm : certMode (⟨216, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨216, by omega⟩ : Fin 1104) = 203876076544910126770526520379 := by decide +kernel
  have he : certE (⟨216, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨216, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨216, by omega⟩ : Fin 1104)).2.2 = 21067420880 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_217 :
    ((certNum ⟨217, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨217, by omega⟩) ⟨217, by omega⟩ (certE ⟨217, by omega⟩) := by
  have hm : certMode (⟨217, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨217, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨217, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨217, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨217, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_218 :
    ((certNum ⟨218, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨218, by omega⟩) ⟨218, by omega⟩ (certE ⟨218, by omega⟩) := by
  have hm : certMode (⟨218, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨218, by omega⟩ : Fin 1104) = 32569946439154608877915352 := by decide +kernel
  have he : certE (⟨218, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -6 else if j.val = 1 then -1 else if j.val = 2 then 2 else -6)) := by decide +kernel
  have hp : parent2 (⟨218, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨218, by omega⟩ : Fin 1104)).2.2 = 1106762 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_219 :
    ((certNum ⟨219, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨219, by omega⟩) ⟨219, by omega⟩ (certE ⟨219, by omega⟩) := by
  have hm : certMode (⟨219, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨219, by omega⟩ : Fin 1104) = 32560401332202079907046793 := by decide +kernel
  have he : certE (⟨219, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -5 else if j.val = 1 then 6 else if j.val = 2 then -2 else -7)) := by decide +kernel
  have hp : parent2 (⟨219, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨219, by omega⟩ : Fin 1104)).2.2 = 1106414 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_220 :
    ((certNum ⟨220, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨220, by omega⟩) ⟨220, by omega⟩ (certE ⟨220, by omega⟩) := by
  have hm : certMode (⟨220, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨220, by omega⟩ : Fin 1104) = 31659233465755191480585477 := by decide +kernel
  have he : certE (⟨220, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -29 else if j.val = 1 then -6 else if j.val = 2 then 2 else 5)) := by decide +kernel
  have hp : parent2 (⟨220, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨220, by omega⟩ : Fin 1104)).2.2 = 1073595 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_221 :
    ((certNum ⟨221, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨221, by omega⟩) ⟨221, by omega⟩ (certE ⟨221, by omega⟩) := by
  have hm : certMode (⟨221, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨221, by omega⟩ : Fin 1104) = 31659233465755191480585477 := by decide +kernel
  have he : certE (⟨221, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -29 else if j.val = 1 then -6 else if j.val = 2 then 2 else 5)) := by decide +kernel
  have hp : parent2 (⟨221, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨221, by omega⟩ : Fin 1104)).2.2 = 1073595 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_222 :
    ((certNum ⟨222, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨222, by omega⟩) ⟨222, by omega⟩ (certE ⟨222, by omega⟩) := by
  have hm : certMode (⟨222, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨222, by omega⟩ : Fin 1104) = 32560319045429800186709305 := by decide +kernel
  have he : certE (⟨222, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -5 else if j.val = 1 then 6 else if j.val = 2 then -2 else -7)) := by decide +kernel
  have hp : parent2 (⟨222, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨222, by omega⟩ : Fin 1104)).2.2 = 1106411 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_223 :
    ((certNum ⟨223, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨223, by omega⟩) ⟨223, by omega⟩ (certE ⟨223, by omega⟩) := by
  have hm : certMode (⟨223, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨223, by omega⟩ : Fin 1104) = 32569699585946647298024024 := by decide +kernel
  have he : certE (⟨223, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -6 else if j.val = 1 then -1 else if j.val = 2 then 2 else -6)) := by decide +kernel
  have hp : parent2 (⟨223, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨223, by omega⟩ : Fin 1104)).2.2 = 1106753 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_224 :
    ((certNum ⟨224, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨224, by omega⟩) ⟨224, by omega⟩ (certE ⟨224, by omega⟩) := by
  have hm : certMode (⟨224, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨224, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨224, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨224, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨224, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_225 :
    ((certNum ⟨225, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨225, by omega⟩) ⟨225, by omega⟩ (certE ⟨225, by omega⟩) := by
  have hm : certMode (⟨225, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨225, by omega⟩ : Fin 1104) = 203947030239869676479612709412 := by decide +kernel
  have he : certE (⟨225, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨225, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨225, by omega⟩ : Fin 1104)).2.2 = 21076716103 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_226 :
    ((certNum ⟨226, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨226, by omega⟩) ⟨226, by omega⟩ (certE ⟨226, by omega⟩) := by
  have hm : certMode (⟨226, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨226, by omega⟩ : Fin 1104) = 152437405859965584803914199 := by decide +kernel
  have he : certE (⟨226, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -19 else if j.val = 1 then -6 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hp : parent2 (⟨226, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨226, by omega⟩ : Fin 1104)).2.2 = 5840184 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_227 :
    ((certNum ⟨227, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨227, by omega⟩) ⟨227, by omega⟩ (certE ⟨227, by omega⟩) := by
  have hm : certMode (⟨227, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨227, by omega⟩ : Fin 1104) = 203948603403357586703636940787 := by decide +kernel
  have he : certE (⟨227, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨227, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨227, by omega⟩ : Fin 1104)).2.2 = 21076922209 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_228 :
    ((certNum ⟨228, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨228, by omega⟩) ⟨228, by omega⟩ (certE ⟨228, by omega⟩) := by
  have hm : certMode (⟨228, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨228, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨228, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨228, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨228, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_229 :
    ((certNum ⟨229, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨229, by omega⟩) ⟨229, by omega⟩ (certE ⟨229, by omega⟩) := by
  have hm : certMode (⟨229, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨229, by omega⟩ : Fin 1104) = 203946572530499236619697782600 := by decide +kernel
  have he : certE (⟨229, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨229, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨229, by omega⟩ : Fin 1104)).2.2 = 21076656137 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_230 :
    ((certNum ⟨230, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨230, by omega⟩) ⟨230, by omega⟩ (certE ⟨230, by omega⟩) := by
  have hm : certMode (⟨230, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨230, by omega⟩ : Fin 1104) = 180602449754821543746914542522 := by decide +kernel
  have he : certE (⟨230, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨230, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨230, by omega⟩ : Fin 1104)).2.2 = 18079499042 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_231 :
    ((certNum ⟨231, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨231, by omega⟩) ⟨231, by omega⟩ (certE ⟨231, by omega⟩) := by
  have hm : certMode (⟨231, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨231, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨231, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨231, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨231, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_232 :
    ((certNum ⟨232, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨232, by omega⟩) ⟨232, by omega⟩ (certE ⟨232, by omega⟩) := by
  have hm : certMode (⟨232, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨232, by omega⟩ : Fin 1104) = 180608939893089921270292247734 := by decide +kernel
  have he : certE (⟨232, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -7 else if j.val = 1 then 4 else if j.val = 2 then -1 else -1)) := by decide +kernel
  have hp : parent2 (⟨232, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨232, by omega⟩ : Fin 1104)).2.2 = 18080315185 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_233 :
    ((certNum ⟨233, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨233, by omega⟩) ⟨233, by omega⟩ (certE ⟨233, by omega⟩) := by
  have hm : certMode (⟨233, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨233, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨233, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨233, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨233, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_234 :
    ((certNum ⟨234, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨234, by omega⟩) ⟨234, by omega⟩ (certE ⟨234, by omega⟩) := by
  have hm : certMode (⟨234, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨234, by omega⟩ : Fin 1104) = 53328038812929862770470842237 := by decide +kernel
  have he : certE (⟨234, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -27 else if j.val = 1 then -5 else if j.val = 2 then 8 else 3)) := by decide +kernel
  have hp : parent2 (⟨234, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨234, by omega⟩ : Fin 1104)).2.2 = 4108041152 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_235 :
    ((certNum ⟨235, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨235, by omega⟩) ⟨235, by omega⟩ (certE ⟨235, by omega⟩) := by
  have hm : certMode (⟨235, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨235, by omega⟩ : Fin 1104) = 203865865257415013394264908833 := by decide +kernel
  have he : certE (⟨235, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨235, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨235, by omega⟩ : Fin 1104)).2.2 = 21066083239 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_236 :
    ((certNum ⟨236, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨236, by omega⟩) ⟨236, by omega⟩ (certE ⟨236, by omega⟩) := by
  have hm : certMode (⟨236, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨236, by omega⟩ : Fin 1104) = 203945826421328234878847253611 := by decide +kernel
  have he : certE (⟨236, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨236, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨236, by omega⟩ : Fin 1104)).2.2 = 21076558387 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_237 :
    ((certNum ⟨237, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨237, by omega⟩) ⟨237, by omega⟩ (certE ⟨237, by omega⟩) := by
  have hm : certMode (⟨237, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨237, by omega⟩ : Fin 1104) = 169599130781072644487218888315 := by decide +kernel
  have he : certE (⟨237, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then -33 else if j.val = 1 then 8 else if j.val = 2 then 5 else 1)) := by decide +kernel
  have hp : parent2 (⟨237, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨237, by omega⟩ : Fin 1104)).2.2 = 16709715401 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_238 :
    ((certNum ⟨238, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨238, by omega⟩) ⟨238, by omega⟩ (certE ⟨238, by omega⟩) := by
  have hm : certMode (⟨238, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨238, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨238, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨238, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨238, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_239 :
    ((certNum ⟨239, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨239, by omega⟩) ⟨239, by omega⟩ (certE ⟨239, by omega⟩) := by
  have hm : certMode (⟨239, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨239, by omega⟩ : Fin 1104) = 203945800500202187698760950803 := by decide +kernel
  have he : certE (⟨239, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨239, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨239, by omega⟩ : Fin 1104)).2.2 = 21076554991 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_240 :
    ((certNum ⟨240, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨240, by omega⟩) ⟨240, by omega⟩ (certE ⟨240, by omega⟩) := by
  have hm : certMode (⟨240, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨240, by omega⟩ : Fin 1104) = 53327637517732446039599500296 := by decide +kernel
  have he : certE (⟨240, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -27 else if j.val = 1 then -5 else if j.val = 2 then 8 else 3)) := by decide +kernel
  have hp : parent2 (⟨240, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨240, by omega⟩ : Fin 1104)).2.2 = 4108004581 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_241 :
    ((certNum ⟨241, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨241, by omega⟩) ⟨241, by omega⟩ (certE ⟨241, by omega⟩) := by
  have hm : certMode (⟨241, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨241, by omega⟩ : Fin 1104) = 203774644862109982989043945810 := by decide +kernel
  have he : certE (⟨241, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨241, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨241, by omega⟩ : Fin 1104)).2.2 = 21054134930 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_242 :
    ((certNum ⟨242, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨242, by omega⟩) ⟨242, by omega⟩ (certE ⟨242, by omega⟩) := by
  have hm : certMode (⟨242, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨242, by omega⟩ : Fin 1104) = 204037212987971324952780973516 := by decide +kernel
  have he : certE (⟨242, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -3 else if j.val = 1 then -7 else if j.val = 2 then -6 else 8)) := by decide +kernel
  have hp : parent2 (⟨242, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨242, by omega⟩ : Fin 1104)).2.2 = 21088532119 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_243 :
    ((certNum ⟨243, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨243, by omega⟩) ⟨243, by omega⟩ (certE ⟨243, by omega⟩) := by
  have hm : certMode (⟨243, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨243, by omega⟩ : Fin 1104) = 169645564250648229034705263068 := by decide +kernel
  have he : certE (⟨243, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 13 else if j.val = 1 then -6 else if j.val = 2 then 2 else -5)) := by decide +kernel
  have hp : parent2 (⟨243, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨243, by omega⟩ : Fin 1104)).2.2 = 16715437197 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_244 :
    ((certNum ⟨244, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨244, by omega⟩) ⟨244, by omega⟩ (certE ⟨244, by omega⟩) := by
  have hm : certMode (⟨244, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨244, by omega⟩ : Fin 1104) = 203774680418434111017891166093 := by decide +kernel
  have he : certE (⟨244, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨244, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨244, by omega⟩ : Fin 1104)).2.2 = 21054139587 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_245 :
    ((certNum ⟨245, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨245, by omega⟩) ⟨245, by omega⟩ (certE ⟨245, by omega⟩) := by
  have hm : certMode (⟨245, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨245, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨245, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨245, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨245, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_246 :
    ((certNum ⟨246, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨246, by omega⟩) ⟨246, by omega⟩ (certE ⟨246, by omega⟩) := by
  have hm : certMode (⟨246, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨246, by omega⟩ : Fin 1104) = 196701651018427659518336641910 := by decide +kernel
  have he : certE (⟨246, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -32 else if j.val = 1 then 1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨246, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨246, by omega⟩ : Fin 1104)).2.2 = 20133361918 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_247 :
    ((certNum ⟨247, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨247, by omega⟩) ⟨247, by omega⟩ (certE ⟨247, by omega⟩) := by
  have hm : certMode (⟨247, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨247, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨247, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨247, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨247, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_248 :
    ((certNum ⟨248, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨248, by omega⟩) ⟨248, by omega⟩ (certE ⟨248, by omega⟩) := by
  have hm : certMode (⟨248, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨248, by omega⟩ : Fin 1104) = 4008083046445890796953209 := by decide +kernel
  have he : certE (⟨248, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -23 else if j.val = 1 then 5 else if j.val = 2 then -1 else -2)) := by decide +kernel
  have hp : parent2 (⟨248, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨248, by omega⟩ : Fin 1104)).2.2 = 118228 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_249 :
    ((certNum ⟨249, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨249, by omega⟩) ⟨249, by omega⟩ (certE ⟨249, by omega⟩) := by
  have hm : certMode (⟨249, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨249, by omega⟩ : Fin 1104) = 196701652185424076800342032957 := by decide +kernel
  have he : certE (⟨249, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -32 else if j.val = 1 then 1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨249, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨249, by omega⟩ : Fin 1104)).2.2 = 20133362069 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_250 :
    ((certNum ⟨250, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨250, by omega⟩) ⟨250, by omega⟩ (certE ⟨250, by omega⟩) := by
  have hm : certMode (⟨250, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨250, by omega⟩ : Fin 1104) = 3966597008440465196274714 := by decide +kernel
  have he : certE (⟨250, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -35 else if j.val = 1 then 2 else if j.val = 2 then 5 else -1)) := by decide +kernel
  have hp : parent2 (⟨250, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨250, by omega⟩ : Fin 1104)).2.2 = 116928 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_251 :
    ((certNum ⟨251, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨251, by omega⟩) ⟨251, by omega⟩ (certE ⟨251, by omega⟩) := by
  have hm : certMode (⟨251, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨251, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨251, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨251, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨251, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_252 :
    ((certNum ⟨252, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨252, by omega⟩) ⟨252, by omega⟩ (certE ⟨252, by omega⟩) := by
  have hm : certMode (⟨252, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨252, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨252, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨252, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨252, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_253 :
    ((certNum ⟨253, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨253, by omega⟩) ⟨253, by omega⟩ (certE ⟨253, by omega⟩) := by
  have hm : certMode (⟨253, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨253, by omega⟩ : Fin 1104) = 202779594022666996799972341917 := by decide +kernel
  have he : certE (⟨253, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨253, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨253, by omega⟩ : Fin 1104)).2.2 = 20923922375 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_254 :
    ((certNum ⟨254, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨254, by omega⟩) ⟨254, by omega⟩ (certE ⟨254, by omega⟩) := by
  have hm : certMode (⟨254, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨254, by omega⟩ : Fin 1104) = 190815285215888226576446323010 := by decide +kernel
  have he : certE (⟨254, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨254, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨254, by omega⟩ : Fin 1104)).2.2 = 19375615127 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_255 :
    ((certNum ⟨255, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨255, by omega⟩) ⟨255, by omega⟩ (certE ⟨255, by omega⟩) := by
  have hm : certMode (⟨255, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨255, by omega⟩ : Fin 1104) = 90542332085497825264400811680 := by decide +kernel
  have he : certE (⟨255, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then -28 else if j.val = 1 then 2 else if j.val = 2 then -2 else 8)) := by decide +kernel
  have hp : parent2 (⟨255, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨255, by omega⟩ : Fin 1104)).2.2 = 7732676516 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_256 :
    ((certNum ⟨256, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨256, by omega⟩) ⟨256, by omega⟩ (certE ⟨256, by omega⟩) := by
  have hm : certMode (⟨256, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨256, by omega⟩ : Fin 1104) = 202779605785524450853134281155 := by decide +kernel
  have he : certE (⟨256, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨256, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨256, by omega⟩ : Fin 1104)).2.2 = 20923923913 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_257 :
    ((certNum ⟨257, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨257, by omega⟩) ⟨257, by omega⟩ (certE ⟨257, by omega⟩) := by
  have hm : certMode (⟨257, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨257, by omega⟩ : Fin 1104) = 181360516599926397439715840535 := by decide +kernel
  have he : certE (⟨257, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then -3 else 6)) := by decide +kernel
  have hp : parent2 (⟨257, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨257, by omega⟩ : Fin 1104)).2.2 = 18174891448 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_258 :
    ((certNum ⟨258, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨258, by omega⟩) ⟨258, by omega⟩ (certE ⟨258, by omega⟩) := by
  have hm : certMode (⟨258, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨258, by omega⟩ : Fin 1104) = 203305763766613292316247976112 := by decide +kernel
  have he : certE (⟨258, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨258, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨258, by omega⟩ : Fin 1104)).2.2 = 20992749931 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_259 :
    ((certNum ⟨259, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨259, by omega⟩) ⟨259, by omega⟩ (certE ⟨259, by omega⟩) := by
  have hm : certMode (⟨259, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨259, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨259, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨259, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨259, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_260 :
    ((certNum ⟨260, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨260, by omega⟩) ⟨260, by omega⟩ (certE ⟨260, by omega⟩) := by
  have hm : certMode (⟨260, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨260, by omega⟩ : Fin 1104) = 190863935294284153908466055142 := by decide +kernel
  have he : certE (⟨260, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hp : parent2 (⟨260, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨260, by omega⟩ : Fin 1104)).2.2 = 19381845916 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_261 :
    ((certNum ⟨261, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨261, by omega⟩) ⟨261, by omega⟩ (certE ⟨261, by omega⟩) := by
  have hm : certMode (⟨261, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨261, by omega⟩ : Fin 1104) = 203305760251568500267276622842 := by decide +kernel
  have he : certE (⟨261, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨261, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨261, by omega⟩ : Fin 1104)).2.2 = 20992749471 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_262 :
    ((certNum ⟨262, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨262, by omega⟩) ⟨262, by omega⟩ (certE ⟨262, by omega⟩) := by
  have hm : certMode (⟨262, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨262, by omega⟩ : Fin 1104) = 89384187787757716341881805379 := by decide +kernel
  have he : certE (⟨262, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 8 else if j.val = 1 then 7 else if j.val = 2 then -4 else -6)) := by decide +kernel
  have hp : parent2 (⟨262, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨262, by omega⟩ : Fin 1104)).2.2 = 7613392991 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_263 :
    ((certNum ⟨263, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨263, by omega⟩) ⟨263, by omega⟩ (certE ⟨263, by omega⟩) := by
  have hm : certMode (⟨263, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨263, by omega⟩ : Fin 1104) = 181577074325446313535942350374 := by decide +kernel
  have he : certE (⟨263, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 13 else if j.val = 1 then -8 else if j.val = 2 then 1 else -3)) := by decide +kernel
  have hp : parent2 (⟨263, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨263, by omega⟩ : Fin 1104)).2.2 = 18202166175 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_264 :
    ((certNum ⟨264, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨264, by omega⟩) ⟨264, by omega⟩ (certE ⟨264, by omega⟩) := by
  have hm : certMode (⟨264, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨264, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨264, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨264, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨264, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_265 :
    ((certNum ⟨265, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨265, by omega⟩) ⟨265, by omega⟩ (certE ⟨265, by omega⟩) := by
  have hm : certMode (⟨265, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨265, by omega⟩ : Fin 1104) = 154660142325986494559495150652 := by decide +kernel
  have he : certE (⟨265, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -15 else if j.val = 1 then 1 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨265, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨265, by omega⟩ : Fin 1104)).2.2 = 14894983498 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_266 :
    ((certNum ⟨266, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨266, by omega⟩) ⟨266, by omega⟩ (certE ⟨266, by omega⟩) := by
  have hm : certMode (⟨266, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨266, by omega⟩ : Fin 1104) = 203945290824452165657914981641 := by decide +kernel
  have he : certE (⟨266, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨266, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨266, by omega⟩ : Fin 1104)).2.2 = 21076488217 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_267 :
    ((certNum ⟨267, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨267, by omega⟩) ⟨267, by omega⟩ (certE ⟨267, by omega⟩) := by
  have hm : certMode (⟨267, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨267, by omega⟩ : Fin 1104) = 203973292667184783931775255584 := by decide +kernel
  have he : certE (⟨267, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 1 else if j.val = 1 then -2 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hp : parent2 (⟨267, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨267, by omega⟩ : Fin 1104)).2.2 = 21080156892 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_268 :
    ((certNum ⟨268, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨268, by omega⟩) ⟨268, by omega⟩ (certE ⟨268, by omega⟩) := by
  have hm : certMode (⟨268, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨268, by omega⟩ : Fin 1104) = 23025350332009014249535669868 := by decide +kernel
  have he : certE (⟨268, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then -29 else if j.val = 1 then 3 else if j.val = 2 then 4 else 2)) := by decide +kernel
  have hp : parent2 (⟨268, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨268, by omega⟩ : Fin 1104)).2.2 = 1540316871 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_269 :
    ((certNum ⟨269, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨269, by omega⟩) ⟨269, by omega⟩ (certE ⟨269, by omega⟩) := by
  have hm : certMode (⟨269, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨269, by omega⟩ : Fin 1104) = 203945851953177187043243208896 := by decide +kernel
  have he : certE (⟨269, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨269, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨269, by omega⟩ : Fin 1104)).2.2 = 21076561732 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_270 :
    ((certNum ⟨270, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨270, by omega⟩) ⟨270, by omega⟩ (certE ⟨270, by omega⟩) := by
  have hm : certMode (⟨270, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨270, by omega⟩ : Fin 1104) = 203880848788542000255003993670 := by decide +kernel
  have he : certE (⟨270, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨270, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨270, by omega⟩ : Fin 1104)).2.2 = 21068046035 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_271 :
    ((certNum ⟨271, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨271, by omega⟩) ⟨271, by omega⟩ (certE ⟨271, by omega⟩) := by
  have hm : certMode (⟨271, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨271, by omega⟩ : Fin 1104) = 23026695232435997663956198238 := by decide +kernel
  have he : certE (⟨271, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then 18 else if j.val = 1 then -4 else if j.val = 2 then -3 else -5)) := by decide +kernel
  have hp : parent2 (⟨271, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨271, by omega⟩ : Fin 1104)).2.2 = 1540420761 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_272 :
    ((certNum ⟨272, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨272, by omega⟩) ⟨272, by omega⟩ (certE ⟨272, by omega⟩) := by
  have hm : certMode (⟨272, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨272, by omega⟩ : Fin 1104) = 204038459607163317568666745999 := by decide +kernel
  have he : certE (⟨272, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨272, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨272, by omega⟩ : Fin 1104)).2.2 = 21088695469 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_273 :
    ((certNum ⟨273, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨273, by omega⟩) ⟨273, by omega⟩ (certE ⟨273, by omega⟩) := by
  have hm : certMode (⟨273, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨273, by omega⟩ : Fin 1104) = 203879475684062037125300412817 := by decide +kernel
  have he : certE (⟨273, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨273, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨273, by omega⟩ : Fin 1104)).2.2 = 21067866165 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_274 :
    ((certNum ⟨274, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨274, by omega⟩) ⟨274, by omega⟩ (certE ⟨274, by omega⟩) := by
  have hm : certMode (⟨274, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨274, by omega⟩ : Fin 1104) = 154679957241268300808058245870 := by decide +kernel
  have he : certE (⟨274, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -19 else if j.val = 1 then 7 else if j.val = 2 then 2 else -1)) := by decide +kernel
  have hp : parent2 (⟨274, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨274, by omega⟩ : Fin 1104)).2.2 = 14897355785 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_275 :
    ((certNum ⟨275, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨275, by omega⟩) ⟨275, by omega⟩ (certE ⟨275, by omega⟩) := by
  have hm : certMode (⟨275, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨275, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨275, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨275, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨275, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨184 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨184 + j.val, by omega⟩) ⟨184 + j.val, by omega⟩
        (certE ⟨184 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_184
  | ⟨1, _⟩ => exact MME.L2Cert.cert_185
  | ⟨2, _⟩ => exact MME.L2Cert.cert_186
  | ⟨3, _⟩ => exact MME.L2Cert.cert_187
  | ⟨4, _⟩ => exact MME.L2Cert.cert_188
  | ⟨5, _⟩ => exact MME.L2Cert.cert_189
  | ⟨6, _⟩ => exact MME.L2Cert.cert_190
  | ⟨7, _⟩ => exact MME.L2Cert.cert_191
  | ⟨8, _⟩ => exact MME.L2Cert.cert_192
  | ⟨9, _⟩ => exact MME.L2Cert.cert_193
  | ⟨10, _⟩ => exact MME.L2Cert.cert_194
  | ⟨11, _⟩ => exact MME.L2Cert.cert_195
  | ⟨12, _⟩ => exact MME.L2Cert.cert_196
  | ⟨13, _⟩ => exact MME.L2Cert.cert_197
  | ⟨14, _⟩ => exact MME.L2Cert.cert_198
  | ⟨15, _⟩ => exact MME.L2Cert.cert_199
  | ⟨16, _⟩ => exact MME.L2Cert.cert_200
  | ⟨17, _⟩ => exact MME.L2Cert.cert_201
  | ⟨18, _⟩ => exact MME.L2Cert.cert_202
  | ⟨19, _⟩ => exact MME.L2Cert.cert_203
  | ⟨20, _⟩ => exact MME.L2Cert.cert_204
  | ⟨21, _⟩ => exact MME.L2Cert.cert_205
  | ⟨22, _⟩ => exact MME.L2Cert.cert_206
  | ⟨23, _⟩ => exact MME.L2Cert.cert_207
  | ⟨24, _⟩ => exact MME.L2Cert.cert_208
  | ⟨25, _⟩ => exact MME.L2Cert.cert_209
  | ⟨26, _⟩ => exact MME.L2Cert.cert_210
  | ⟨27, _⟩ => exact MME.L2Cert.cert_211
  | ⟨28, _⟩ => exact MME.L2Cert.cert_212
  | ⟨29, _⟩ => exact MME.L2Cert.cert_213
  | ⟨30, _⟩ => exact MME.L2Cert.cert_214
  | ⟨31, _⟩ => exact MME.L2Cert.cert_215
  | ⟨32, _⟩ => exact MME.L2Cert.cert_216
  | ⟨33, _⟩ => exact MME.L2Cert.cert_217
  | ⟨34, _⟩ => exact MME.L2Cert.cert_218
  | ⟨35, _⟩ => exact MME.L2Cert.cert_219
  | ⟨36, _⟩ => exact MME.L2Cert.cert_220
  | ⟨37, _⟩ => exact MME.L2Cert.cert_221
  | ⟨38, _⟩ => exact MME.L2Cert.cert_222
  | ⟨39, _⟩ => exact MME.L2Cert.cert_223
  | ⟨40, _⟩ => exact MME.L2Cert.cert_224
  | ⟨41, _⟩ => exact MME.L2Cert.cert_225
  | ⟨42, _⟩ => exact MME.L2Cert.cert_226
  | ⟨43, _⟩ => exact MME.L2Cert.cert_227
  | ⟨44, _⟩ => exact MME.L2Cert.cert_228
  | ⟨45, _⟩ => exact MME.L2Cert.cert_229
  | ⟨46, _⟩ => exact MME.L2Cert.cert_230
  | ⟨47, _⟩ => exact MME.L2Cert.cert_231
  | ⟨48, _⟩ => exact MME.L2Cert.cert_232
  | ⟨49, _⟩ => exact MME.L2Cert.cert_233
  | ⟨50, _⟩ => exact MME.L2Cert.cert_234
  | ⟨51, _⟩ => exact MME.L2Cert.cert_235
  | ⟨52, _⟩ => exact MME.L2Cert.cert_236
  | ⟨53, _⟩ => exact MME.L2Cert.cert_237
  | ⟨54, _⟩ => exact MME.L2Cert.cert_238
  | ⟨55, _⟩ => exact MME.L2Cert.cert_239
  | ⟨56, _⟩ => exact MME.L2Cert.cert_240
  | ⟨57, _⟩ => exact MME.L2Cert.cert_241
  | ⟨58, _⟩ => exact MME.L2Cert.cert_242
  | ⟨59, _⟩ => exact MME.L2Cert.cert_243
  | ⟨60, _⟩ => exact MME.L2Cert.cert_244
  | ⟨61, _⟩ => exact MME.L2Cert.cert_245
  | ⟨62, _⟩ => exact MME.L2Cert.cert_246
  | ⟨63, _⟩ => exact MME.L2Cert.cert_247
  | ⟨64, _⟩ => exact MME.L2Cert.cert_248
  | ⟨65, _⟩ => exact MME.L2Cert.cert_249
  | ⟨66, _⟩ => exact MME.L2Cert.cert_250
  | ⟨67, _⟩ => exact MME.L2Cert.cert_251
  | ⟨68, _⟩ => exact MME.L2Cert.cert_252
  | ⟨69, _⟩ => exact MME.L2Cert.cert_253
  | ⟨70, _⟩ => exact MME.L2Cert.cert_254
  | ⟨71, _⟩ => exact MME.L2Cert.cert_255
  | ⟨72, _⟩ => exact MME.L2Cert.cert_256
  | ⟨73, _⟩ => exact MME.L2Cert.cert_257
  | ⟨74, _⟩ => exact MME.L2Cert.cert_258
  | ⟨75, _⟩ => exact MME.L2Cert.cert_259
  | ⟨76, _⟩ => exact MME.L2Cert.cert_260
  | ⟨77, _⟩ => exact MME.L2Cert.cert_261
  | ⟨78, _⟩ => exact MME.L2Cert.cert_262
  | ⟨79, _⟩ => exact MME.L2Cert.cert_263
  | ⟨80, _⟩ => exact MME.L2Cert.cert_264
  | ⟨81, _⟩ => exact MME.L2Cert.cert_265
  | ⟨82, _⟩ => exact MME.L2Cert.cert_266
  | ⟨83, _⟩ => exact MME.L2Cert.cert_267
  | ⟨84, _⟩ => exact MME.L2Cert.cert_268
  | ⟨85, _⟩ => exact MME.L2Cert.cert_269
  | ⟨86, _⟩ => exact MME.L2Cert.cert_270
  | ⟨87, _⟩ => exact MME.L2Cert.cert_271
  | ⟨88, _⟩ => exact MME.L2Cert.cert_272
  | ⟨89, _⟩ => exact MME.L2Cert.cert_273
  | ⟨90, _⟩ => exact MME.L2Cert.cert_274
  | ⟨91, _⟩ => exact MME.L2Cert.cert_275
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
