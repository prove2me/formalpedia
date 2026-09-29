-- Prove2me | solution 1 for mme_released_recursive_level2_cert6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:33:11.342894+00:00
-- url     : https://prove2.me/submissions/3628e9f7-a725-486d-b7bf-e4616d5588a8

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

theorem cert_552 :
    ((certNum ⟨552, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨552, by omega⟩) ⟨552, by omega⟩ (certE ⟨552, by omega⟩) := by
  have hm : certMode (⟨552, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨552, by omega⟩ : Fin 1104) = 179531375792789324808801643181 := by decide +kernel
  have he : certE (⟨552, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hp : parent2 (⟨552, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨552, by omega⟩ : Fin 1104)).2.2 = 17944942492 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_553 :
    ((certNum ⟨553, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨553, by omega⟩) ⟨553, by omega⟩ (certE ⟨553, by omega⟩) := by
  have hm : certMode (⟨553, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨553, by omega⟩ : Fin 1104) = 179530430355245373727161256821 := by decide +kernel
  have he : certE (⟨553, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hp : parent2 (⟨553, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨553, by omega⟩ : Fin 1104)).2.2 = 17944823834 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_554 :
    ((certNum ⟨554, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨554, by omega⟩) ⟨554, by omega⟩ (certE ⟨554, by omega⟩) := by
  have hm : certMode (⟨554, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨554, by omega⟩ : Fin 1104) = 179531769972466013758194349013 := by decide +kernel
  have he : certE (⟨554, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hp : parent2 (⟨554, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨554, by omega⟩ : Fin 1104)).2.2 = 17944991964 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_555 :
    ((certNum ⟨555, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨555, by omega⟩) ⟨555, by omega⟩ (certE ⟨555, by omega⟩) := by
  have hm : certMode (⟨555, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨555, by omega⟩ : Fin 1104) = 179530218563977079804026959356 := by decide +kernel
  have he : certE (⟨555, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hp : parent2 (⟨555, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨555, by omega⟩ : Fin 1104)).2.2 = 17944797253 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_556 :
    ((certNum ⟨556, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨556, by omega⟩) ⟨556, by omega⟩ (certE ⟨556, by omega⟩) := by
  have hm : certMode (⟨556, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨556, by omega⟩ : Fin 1104) = 179529717135685948203449825796 := by decide +kernel
  have he : certE (⟨556, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hp : parent2 (⟨556, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨556, by omega⟩ : Fin 1104)).2.2 = 17944734321 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_557 :
    ((certNum ⟨557, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨557, by omega⟩) ⟨557, by omega⟩ (certE ⟨557, by omega⟩) := by
  have hm : certMode (⟨557, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨557, by omega⟩ : Fin 1104) = 179529714928609039400685809938 := by decide +kernel
  have he : certE (⟨557, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -13 else if j.val = 1 then 1 else if j.val = 2 then 0 else 2)) := by decide +kernel
  have hp : parent2 (⟨557, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨557, by omega⟩ : Fin 1104)).2.2 = 17944734044 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_558 :
    ((certNum ⟨558, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨558, by omega⟩) ⟨558, by omega⟩ (certE ⟨558, by omega⟩) := by
  have hm : certMode (⟨558, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨558, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨558, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨558, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨558, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_559 :
    ((certNum ⟨559, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨559, by omega⟩) ⟨559, by omega⟩ (certE ⟨559, by omega⟩) := by
  have hm : certMode (⟨559, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨559, by omega⟩ : Fin 1104) = 203944513508840966418702617061 := by decide +kernel
  have he : certE (⟨559, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨559, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨559, by omega⟩ : Fin 1104)).2.2 = 21076386379 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_560 :
    ((certNum ⟨560, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨560, by omega⟩) ⟨560, by omega⟩ (certE ⟨560, by omega⟩) := by
  have hm : certMode (⟨560, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨560, by omega⟩ : Fin 1104) = 180553359232116908894157979234 := by decide +kernel
  have he : certE (⟨560, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then 5 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hp : parent2 (⟨560, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨560, by omega⟩ : Fin 1104)).2.2 = 18073326128 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_561 :
    ((certNum ⟨561, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨561, by omega⟩) ⟨561, by omega⟩ (certE ⟨561, by omega⟩) := by
  have hm : certMode (⟨561, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨561, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨561, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨561, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨561, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_562 :
    ((certNum ⟨562, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨562, by omega⟩) ⟨562, by omega⟩ (certE ⟨562, by omega⟩) := by
  have hm : certMode (⟨562, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨562, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨562, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨562, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨562, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_563 :
    ((certNum ⟨563, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨563, by omega⟩) ⟨563, by omega⟩ (certE ⟨563, by omega⟩) := by
  have hm : certMode (⟨563, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨563, by omega⟩ : Fin 1104) = 203944036537780764421479576777 := by decide +kernel
  have he : certE (⟨563, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨563, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨563, by omega⟩ : Fin 1104)).2.2 = 21076323890 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_564 :
    ((certNum ⟨564, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨564, by omega⟩) ⟨564, by omega⟩ (certE ⟨564, by omega⟩) := by
  have hm : certMode (⟨564, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨564, by omega⟩ : Fin 1104) = 147381947312686596257986337 := by decide +kernel
  have he : certE (⟨564, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -20 else if j.val = 1 then 4 else if j.val = 2 then 2 else -3)) := by decide +kernel
  have hp : parent2 (⟨564, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨564, by omega⟩ : Fin 1104)).2.2 = 5630742 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_565 :
    ((certNum ⟨565, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨565, by omega⟩) ⟨565, by omega⟩ (certE ⟨565, by omega⟩) := by
  have hm : certMode (⟨565, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨565, by omega⟩ : Fin 1104) = 203942096885154185512322063343 := by decide +kernel
  have he : certE (⟨565, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨565, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨565, by omega⟩ : Fin 1104)).2.2 = 21076069773 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_566 :
    ((certNum ⟨566, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨566, by omega⟩) ⟨566, by omega⟩ (certE ⟨566, by omega⟩) := by
  have hm : certMode (⟨566, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨566, by omega⟩ : Fin 1104) = 180560055968903269367299168255 := by decide +kernel
  have he : certE (⟨566, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then -6 else if j.val = 2 then -6 else 7)) := by decide +kernel
  have hp : parent2 (⟨566, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨566, by omega⟩ : Fin 1104)).2.2 = 18074168182 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_567 :
    ((certNum ⟨567, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨567, by omega⟩) ⟨567, by omega⟩ (certE ⟨567, by omega⟩) := by
  have hm : certMode (⟨567, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨567, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨567, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨567, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨567, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_568 :
    ((certNum ⟨568, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨568, by omega⟩) ⟨568, by omega⟩ (certE ⟨568, by omega⟩) := by
  have hm : certMode (⟨568, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨568, by omega⟩ : Fin 1104) = 10396854496617659034189542520 := by decide +kernel
  have he : certE (⟨568, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -3 else if j.val = 1 then -8 else if j.val = 2 then 7 else -4)) := by decide +kernel
  have hp : parent2 (⟨568, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨568, by omega⟩ : Fin 1104)).2.2 = 619948955 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_569 :
    ((certNum ⟨569, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨569, by omega⟩) ⟨569, by omega⟩ (certE ⟨569, by omega⟩) := by
  have hm : certMode (⟨569, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨569, by omega⟩ : Fin 1104) = 203946043636610940229495062067 := by decide +kernel
  have he : certE (⟨569, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨569, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨569, by omega⟩ : Fin 1104)).2.2 = 21076586845 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_570 :
    ((certNum ⟨570, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨570, by omega⟩) ⟨570, by omega⟩ (certE ⟨570, by omega⟩) := by
  have hm : certMode (⟨570, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨570, by omega⟩ : Fin 1104) = 10397058977621179162300685874 := by decide +kernel
  have he : certE (⟨570, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -3 else if j.val = 1 then -8 else if j.val = 2 then 7 else -4)) := by decide +kernel
  have hp : parent2 (⟨570, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨570, by omega⟩ : Fin 1104)).2.2 = 619962800 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_571 :
    ((certNum ⟨571, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨571, by omega⟩) ⟨571, by omega⟩ (certE ⟨571, by omega⟩) := by
  have hm : certMode (⟨571, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨571, by omega⟩ : Fin 1104) = 203946072397129700879894982064 := by decide +kernel
  have he : certE (⟨571, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨571, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨571, by omega⟩ : Fin 1104)).2.2 = 21076590613 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_572 :
    ((certNum ⟨572, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨572, by omega⟩) ⟨572, by omega⟩ (certE ⟨572, by omega⟩) := by
  have hm : certMode (⟨572, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨572, by omega⟩ : Fin 1104) = 18357948221584877354181845868 := by decide +kernel
  have he : certE (⟨572, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -10 else if j.val = 1 then -8 else if j.val = 2 then 8 else -2)) := by decide +kernel
  have hp : parent2 (⟨572, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨572, by omega⟩ : Fin 1104)).2.2 = 1186608718 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_573 :
    ((certNum ⟨573, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨573, by omega⟩) ⟨573, by omega⟩ (certE ⟨573, by omega⟩) := by
  have hm : certMode (⟨573, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨573, by omega⟩ : Fin 1104) = 203946065466516626232575166397 := by decide +kernel
  have he : certE (⟨573, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨573, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨573, by omega⟩ : Fin 1104)).2.2 = 21076589705 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_574 :
    ((certNum ⟨574, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨574, by omega⟩) ⟨574, by omega⟩ (certE ⟨574, by omega⟩) := by
  have hm : certMode (⟨574, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨574, by omega⟩ : Fin 1104) = 203304061975678927453726967039 := by decide +kernel
  have he : certE (⟨574, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨574, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨574, by omega⟩ : Fin 1104)).2.2 = 20992527225 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_575 :
    ((certNum ⟨575, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨575, by omega⟩) ⟨575, by omega⟩ (certE ⟨575, by omega⟩) := by
  have hm : certMode (⟨575, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨575, by omega⟩ : Fin 1104) = 15740367145360477075251187305 := by decide +kernel
  have he : certE (⟨575, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 12 else if j.val = 1 then 0 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨575, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨575, by omega⟩ : Fin 1104)).2.2 = 994706306 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_576 :
    ((certNum ⟨576, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨576, by omega⟩) ⟨576, by omega⟩ (certE ⟨576, by omega⟩) := by
  have hm : certMode (⟨576, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨576, by omega⟩ : Fin 1104) = 203304033366103807256607507880 := by decide +kernel
  have he : certE (⟨576, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨576, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨576, by omega⟩ : Fin 1104)).2.2 = 20992523481 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_577 :
    ((certNum ⟨577, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨577, by omega⟩) ⟨577, by omega⟩ (certE ⟨577, by omega⟩) := by
  have hm : certMode (⟨577, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨577, by omega⟩ : Fin 1104) = 15741274730335859529637249291 := by decide +kernel
  have he : certE (⟨577, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 12 else if j.val = 1 then 0 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨577, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨577, by omega⟩ : Fin 1104)).2.2 = 994771968 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_578 :
    ((certNum ⟨578, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨578, by omega⟩) ⟨578, by omega⟩ (certE ⟨578, by omega⟩) := by
  have hm : certMode (⟨578, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨578, by omega⟩ : Fin 1104) = 203304078718086578740892656693 := by decide +kernel
  have he : certE (⟨578, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨578, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨578, by omega⟩ : Fin 1104)).2.2 = 20992529416 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_579 :
    ((certNum ⟨579, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨579, by omega⟩) ⟨579, by omega⟩ (certE ⟨579, by omega⟩) := by
  have hm : certMode (⟨579, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨579, by omega⟩ : Fin 1104) = 25359898172085410127803610709 := by decide +kernel
  have he : certE (⟨579, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -7 else if j.val = 1 then -4 else if j.val = 2 then 3 else -1)) := by decide +kernel
  have hp : parent2 (⟨579, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨579, by omega⟩ : Fin 1104)).2.2 = 1722259055 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_580 :
    ((certNum ⟨580, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨580, by omega⟩) ⟨580, by omega⟩ (certE ⟨580, by omega⟩) := by
  have hm : certMode (⟨580, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨580, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨580, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨580, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨580, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_581 :
    ((certNum ⟨581, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨581, by omega⟩) ⟨581, by omega⟩ (certE ⟨581, by omega⟩) := by
  have hm : certMode (⟨581, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨581, by omega⟩ : Fin 1104) = 203946063398018639480492069372 := by decide +kernel
  have he : certE (⟨581, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨581, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨581, by omega⟩ : Fin 1104)).2.2 = 21076589434 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_582 :
    ((certNum ⟨582, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨582, by omega⟩) ⟨582, by omega⟩ (certE ⟨582, by omega⟩) := by
  have hm : certMode (⟨582, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨582, by omega⟩ : Fin 1104) = 203878077796327008592421883653 := by decide +kernel
  have he : certE (⟨582, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨582, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨582, by omega⟩ : Fin 1104)).2.2 = 21067683042 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_583 :
    ((certNum ⟨583, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨583, by omega⟩) ⟨583, by omega⟩ (certE ⟨583, by omega⟩) := by
  have hm : certMode (⟨583, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨583, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨583, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨583, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨583, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_584 :
    ((certNum ⟨584, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨584, by omega⟩) ⟨584, by omega⟩ (certE ⟨584, by omega⟩) := by
  have hm : certMode (⟨584, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨584, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨584, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨584, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨584, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_585 :
    ((certNum ⟨585, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨585, by omega⟩) ⟨585, by omega⟩ (certE ⟨585, by omega⟩) := by
  have hm : certMode (⟨585, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨585, by omega⟩ : Fin 1104) = 203946073244374239548529091104 := by decide +kernel
  have he : certE (⟨585, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨585, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨585, by omega⟩ : Fin 1104)).2.2 = 21076590724 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_586 :
    ((certNum ⟨586, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨586, by omega⟩) ⟨586, by omega⟩ (certE ⟨586, by omega⟩) := by
  have hm : certMode (⟨586, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨586, by omega⟩ : Fin 1104) = 203877573648850383809459785907 := by decide +kernel
  have he : certE (⟨586, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨586, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨586, by omega⟩ : Fin 1104)).2.2 = 21067616999 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_587 :
    ((certNum ⟨587, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨587, by omega⟩) ⟨587, by omega⟩ (certE ⟨587, by omega⟩) := by
  have hm : certMode (⟨587, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨587, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨587, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨587, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨587, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_588 :
    ((certNum ⟨588, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨588, by omega⟩) ⟨588, by omega⟩ (certE ⟨588, by omega⟩) := by
  have hm : certMode (⟨588, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨588, by omega⟩ : Fin 1104) = 203875581691827337283706329136 := by decide +kernel
  have he : certE (⟨588, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨588, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨588, by omega⟩ : Fin 1104)).2.2 = 21067356055 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_589 :
    ((certNum ⟨589, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨589, by omega⟩) ⟨589, by omega⟩ (certE ⟨589, by omega⟩) := by
  have hm : certMode (⟨589, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨589, by omega⟩ : Fin 1104) = 39760124643628937082723229826 := by decide +kernel
  have he : certE (⟨589, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -16 else if j.val = 1 then -2 else if j.val = 2 then 1 else 3)) := by decide +kernel
  have hp : parent2 (⟨589, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨589, by omega⟩ : Fin 1104)).2.2 = 2907481165 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_590 :
    ((certNum ⟨590, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨590, by omega⟩) ⟨590, by omega⟩ (certE ⟨590, by omega⟩) := by
  have hm : certMode (⟨590, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨590, by omega⟩ : Fin 1104) = 203941691957573284153280641969 := by decide +kernel
  have he : certE (⟨590, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨590, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨590, by omega⟩ : Fin 1104)).2.2 = 21076016723 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_591 :
    ((certNum ⟨591, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨591, by omega⟩) ⟨591, by omega⟩ (certE ⟨591, by omega⟩) := by
  have hm : certMode (⟨591, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨591, by omega⟩ : Fin 1104) = 203941723267921863020648943982 := by decide +kernel
  have he : certE (⟨591, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨591, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨591, by omega⟩ : Fin 1104)).2.2 = 21076020825 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_592 :
    ((certNum ⟨592, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨592, by omega⟩) ⟨592, by omega⟩ (certE ⟨592, by omega⟩) := by
  have hm : certMode (⟨592, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨592, by omega⟩ : Fin 1104) = 203941687851047552828819138772 := by decide +kernel
  have he : certE (⟨592, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨592, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨592, by omega⟩ : Fin 1104)).2.2 = 21076016185 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_593 :
    ((certNum ⟨593, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨593, by omega⟩) ⟨593, by omega⟩ (certE ⟨593, by omega⟩) := by
  have hm : certMode (⟨593, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨593, by omega⟩ : Fin 1104) = 203941687881579342864405295639 := by decide +kernel
  have he : certE (⟨593, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨593, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨593, by omega⟩ : Fin 1104)).2.2 = 21076016189 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_594 :
    ((certNum ⟨594, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨594, by omega⟩) ⟨594, by omega⟩ (certE ⟨594, by omega⟩) := by
  have hm : certMode (⟨594, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨594, by omega⟩ : Fin 1104) = 203941721031468503666785777497 := by decide +kernel
  have he : certE (⟨594, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨594, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨594, by omega⟩ : Fin 1104)).2.2 = 21076020532 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_595 :
    ((certNum ⟨595, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨595, by omega⟩) ⟨595, by omega⟩ (certE ⟨595, by omega⟩) := by
  have hm : certMode (⟨595, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨595, by omega⟩ : Fin 1104) = 203941691942307389347496306954 := by decide +kernel
  have he : certE (⟨595, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨595, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨595, by omega⟩ : Fin 1104)).2.2 = 21076016721 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_596 :
    ((certNum ⟨596, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨596, by omega⟩) ⟨596, by omega⟩ (certE ⟨596, by omega⟩) := by
  have hm : certMode (⟨596, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨596, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨596, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨596, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨596, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_597 :
    ((certNum ⟨597, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨597, by omega⟩) ⟨597, by omega⟩ (certE ⟨597, by omega⟩) := by
  have hm : certMode (⟨597, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨597, by omega⟩ : Fin 1104) = 203778687104504761503187041339 := by decide +kernel
  have he : certE (⟨597, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨597, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨597, by omega⟩ : Fin 1104)).2.2 = 21054664354 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_598 :
    ((certNum ⟨598, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨598, by omega⟩) ⟨598, by omega⟩ (certE ⟨598, by omega⟩) := by
  have hm : certMode (⟨598, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨598, by omega⟩ : Fin 1104) = 152373439405756324252816601 := by decide +kernel
  have he : certE (⟨598, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -17 else if j.val = 1 then 8 else if j.val = 2 then -2 else -3)) := by decide +kernel
  have hp : parent2 (⟨598, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨598, by omega⟩ : Fin 1104)).2.2 = 5837530 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_599 :
    ((certNum ⟨599, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨599, by omega⟩) ⟨599, by omega⟩ (certE ⟨599, by omega⟩) := by
  have hm : certMode (⟨599, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨599, by omega⟩ : Fin 1104) = 203781458865370302620973701766 := by decide +kernel
  have he : certE (⟨599, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨599, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨599, by omega⟩ : Fin 1104)).2.2 = 21055027375 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_600 :
    ((certNum ⟨600, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨600, by omega⟩) ⟨600, by omega⟩ (certE ⟨600, by omega⟩) := by
  have hm : certMode (⟨600, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨600, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨600, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨600, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨600, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_601 :
    ((certNum ⟨601, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨601, by omega⟩) ⟨601, by omega⟩ (certE ⟨601, by omega⟩) := by
  have hm : certMode (⟨601, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨601, by omega⟩ : Fin 1104) = 203778024634662754290381493765 := by decide +kernel
  have he : certE (⟨601, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨601, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨601, by omega⟩ : Fin 1104)).2.2 = 21054577590 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_602 :
    ((certNum ⟨602, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨602, by omega⟩) ⟨602, by omega⟩ (certE ⟨602, by omega⟩) := by
  have hm : certMode (⟨602, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨602, by omega⟩ : Fin 1104) = 180553422887000589421937159768 := by decide +kernel
  have he : certE (⟨602, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then 5 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hp : parent2 (⟨602, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨602, by omega⟩ : Fin 1104)).2.2 = 18073334132 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_603 :
    ((certNum ⟨603, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨603, by omega⟩) ⟨603, by omega⟩ (certE ⟨603, by omega⟩) := by
  have hm : certMode (⟨603, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨603, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨603, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨603, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨603, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_604 :
    ((certNum ⟨604, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨604, by omega⟩) ⟨604, by omega⟩ (certE ⟨604, by omega⟩) := by
  have hm : certMode (⟨604, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨604, by omega⟩ : Fin 1104) = 180560371453662980563113438465 := by decide +kernel
  have he : certE (⟨604, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then -6 else if j.val = 2 then -6 else 7)) := by decide +kernel
  have hp : parent2 (⟨604, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨604, by omega⟩ : Fin 1104)).2.2 = 18074207851 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_605 :
    ((certNum ⟨605, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨605, by omega⟩) ⟨605, by omega⟩ (certE ⟨605, by omega⟩) := by
  have hm : certMode (⟨605, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨605, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨605, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨605, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨605, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_606 :
    ((certNum ⟨606, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨606, by omega⟩) ⟨606, by omega⟩ (certE ⟨606, by omega⟩) := by
  have hm : certMode (⟨606, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨606, by omega⟩ : Fin 1104) = 53267537680451378240717729775 := by decide +kernel
  have he : certE (⟨606, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -11 else if j.val = 1 then -6 else if j.val = 2 then 3 else 2)) := by decide +kernel
  have hp : parent2 (⟨606, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨606, by omega⟩ : Fin 1104)).2.2 = 4102528207 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_607 :
    ((certNum ⟨607, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨607, by omega⟩) ⟨607, by omega⟩ (certE ⟨607, by omega⟩) := by
  have hm : certMode (⟨607, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨607, by omega⟩ : Fin 1104) = 204037997814899657515679387235 := by decide +kernel
  have he : certE (⟨607, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -3 else if j.val = 1 then -7 else if j.val = 2 then -6 else 8)) := by decide +kernel
  have hp : parent2 (⟨607, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨607, by omega⟩ : Fin 1104)).2.2 = 21088634959 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_608 :
    ((certNum ⟨608, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨608, by omega⟩) ⟨608, by omega⟩ (certE ⟨608, by omega⟩) := by
  have hm : certMode (⟨608, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨608, by omega⟩ : Fin 1104) = 203776727154855382383760520063 := by decide +kernel
  have he : certE (⟨608, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨608, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨608, by omega⟩ : Fin 1104)).2.2 = 21054407659 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_609 :
    ((certNum ⟨609, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨609, by omega⟩) ⟨609, by omega⟩ (certE ⟨609, by omega⟩) := by
  have hm : certMode (⟨609, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨609, by omega⟩ : Fin 1104) = 169622582540302994206875233561 := by decide +kernel
  have he : certE (⟨609, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 14 else if j.val = 1 then 1 else if j.val = 2 then -2 else -6)) := by decide +kernel
  have hp : parent2 (⟨609, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨609, by omega⟩ : Fin 1104)).2.2 = 16712605197 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_610 :
    ((certNum ⟨610, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨610, by omega⟩) ⟨610, by omega⟩ (certE ⟨610, by omega⟩) := by
  have hm : certMode (⟨610, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨610, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨610, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨610, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨610, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_611 :
    ((certNum ⟨611, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨611, by omega⟩) ⟨611, by omega⟩ (certE ⟨611, by omega⟩) := by
  have hm : certMode (⟨611, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨611, by omega⟩ : Fin 1104) = 203776700270786598241179443118 := by decide +kernel
  have he : certE (⟨611, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨611, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨611, by omega⟩ : Fin 1104)).2.2 = 21054404138 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_612 :
    ((certNum ⟨612, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨612, by omega⟩) ⟨612, by omega⟩ (certE ⟨612, by omega⟩) := by
  have hm : certMode (⟨612, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨612, by omega⟩ : Fin 1104) = 53267720590821945815558073556 := by decide +kernel
  have he : certE (⟨612, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -11 else if j.val = 1 then -6 else if j.val = 2 then 3 else 2)) := by decide +kernel
  have hp : parent2 (⟨612, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨612, by omega⟩ : Fin 1104)).2.2 = 4102544872 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_613 :
    ((certNum ⟨613, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨613, by omega⟩) ⟨613, by omega⟩ (certE ⟨613, by omega⟩) := by
  have hm : certMode (⟨613, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨613, by omega⟩ : Fin 1104) = 203946051895337687551648748530 := by decide +kernel
  have he : certE (⟨613, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨613, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨613, by omega⟩ : Fin 1104)).2.2 = 21076587927 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_614 :
    ((certNum ⟨614, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨614, by omega⟩) ⟨614, by omega⟩ (certE ⟨614, by omega⟩) := by
  have hm : certMode (⟨614, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨614, by omega⟩ : Fin 1104) = 203867995850499479971618829241 := by decide +kernel
  have he : certE (⟨614, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨614, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨614, by omega⟩ : Fin 1104)).2.2 = 21066362335 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_615 :
    ((certNum ⟨615, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨615, by omega⟩) ⟨615, by omega⟩ (certE ⟨615, by omega⟩) := by
  have hm : certMode (⟨615, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨615, by omega⟩ : Fin 1104) = 169574641826858054672291139852 := by decide +kernel
  have he : certE (⟨615, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 15 else if j.val = 1 then 8 else if j.val = 2 then -6 else -7)) := by decide +kernel
  have hp : parent2 (⟨615, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨615, by omega⟩ : Fin 1104)).2.2 = 16706697919 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_616 :
    ((certNum ⟨616, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨616, by omega⟩) ⟨616, by omega⟩ (certE ⟨616, by omega⟩) := by
  have hm : certMode (⟨616, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨616, by omega⟩ : Fin 1104) = 203946080037596128000968335058 := by decide +kernel
  have he : certE (⟨616, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨616, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨616, by omega⟩ : Fin 1104)).2.2 = 21076591614 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_617 :
    ((certNum ⟨617, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨617, by omega⟩) ⟨617, by omega⟩ (certE ⟨617, by omega⟩) := by
  have hm : certMode (⟨617, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨617, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨617, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨617, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨617, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_618 :
    ((certNum ⟨618, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨618, by omega⟩) ⟨618, by omega⟩ (certE ⟨618, by omega⟩) := by
  have hm : certMode (⟨618, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨618, by omega⟩ : Fin 1104) = 196681312797278158252354361918 := by decide +kernel
  have he : certE (⟨618, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -28 else if j.val = 1 then -5 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hp : parent2 (⟨618, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨618, by omega⟩ : Fin 1104)).2.2 = 20130730373 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_619 :
    ((certNum ⟨619, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨619, by omega⟩) ⟨619, by omega⟩ (certE ⟨619, by omega⟩) := by
  have hm : certMode (⟨619, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨619, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨619, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨619, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨619, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_620 :
    ((certNum ⟨620, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨620, by omega⟩) ⟨620, by omega⟩ (certE ⟨620, by omega⟩) := by
  have hm : certMode (⟨620, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨620, by omega⟩ : Fin 1104) = 3965703146563322076578143 := by decide +kernel
  have he : certE (⟨620, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -30 else if j.val = 1 then -8 else if j.val = 2 then 0 else 7)) := by decide +kernel
  have hp : parent2 (⟨620, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨620, by omega⟩ : Fin 1104)).2.2 = 116900 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_621 :
    ((certNum ⟨621, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨621, by omega⟩) ⟨621, by omega⟩ (certE ⟨621, by omega⟩) := by
  have hm : certMode (⟨621, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨621, by omega⟩ : Fin 1104) = 196681312503590524756068669428 := by decide +kernel
  have he : certE (⟨621, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -28 else if j.val = 1 then -5 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hp : parent2 (⟨621, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨621, by omega⟩ : Fin 1104)).2.2 = 20130730335 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_622 :
    ((certNum ⟨622, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨622, by omega⟩) ⟨622, by omega⟩ (certE ⟨622, by omega⟩) := by
  have hm : certMode (⟨622, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨622, by omega⟩ : Fin 1104) = 4725551881457123686871349 := by decide +kernel
  have he : certE (⟨622, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -29 else if j.val = 1 then -4 else if j.val = 2 then 3 else 2)) := by decide +kernel
  have hp : parent2 (⟨622, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨622, by omega⟩ : Fin 1104)).2.2 = 140846 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_623 :
    ((certNum ⟨623, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨623, by omega⟩) ⟨623, by omega⟩ (certE ⟨623, by omega⟩) := by
  have hm : certMode (⟨623, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨623, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨623, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨623, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨623, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_624 :
    ((certNum ⟨624, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨624, by omega⟩) ⟨624, by omega⟩ (certE ⟨624, by omega⟩) := by
  have hm : certMode (⟨624, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨624, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨624, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨624, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨624, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_625 :
    ((certNum ⟨625, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨625, by omega⟩) ⟨625, by omega⟩ (certE ⟨625, by omega⟩) := by
  have hm : certMode (⟨625, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨625, by omega⟩ : Fin 1104) = 203946142428370491633854238657 := by decide +kernel
  have he : certE (⟨625, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨625, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨625, by omega⟩ : Fin 1104)).2.2 = 21076599788 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_626 :
    ((certNum ⟨626, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨626, by omega⟩) ⟨626, by omega⟩ (certE ⟨626, by omega⟩) := by
  have hm : certMode (⟨626, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨626, by omega⟩ : Fin 1104) = 190579320132375650294835027502 := by decide +kernel
  have he : certE (⟨626, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -5 else -3)) := by decide +kernel
  have hp : parent2 (⟨626, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨626, by omega⟩ : Fin 1104)).2.2 = 19345402121 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_627 :
    ((certNum ⟨627, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨627, by omega⟩) ⟨627, by omega⟩ (certE ⟨627, by omega⟩) := by
  have hm : certMode (⟨627, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨627, by omega⟩ : Fin 1104) = 89918841953946730796913908810 := by decide +kernel
  have he : certE (⟨627, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -25 else if j.val = 1 then -6 else if j.val = 2 then 7 else 4)) := by decide +kernel
  have hp : parent2 (⟨627, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨627, by omega⟩ : Fin 1104)).2.2 = 7668411867 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_628 :
    ((certNum ⟨628, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨628, by omega⟩) ⟨628, by omega⟩ (certE ⟨628, by omega⟩) := by
  have hm : certMode (⟨628, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨628, by omega⟩ : Fin 1104) = 203946149565068207935402344416 := by decide +kernel
  have he : certE (⟨628, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨628, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨628, by omega⟩ : Fin 1104)).2.2 = 21076600723 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_629 :
    ((certNum ⟨629, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨629, by omega⟩) ⟨629, by omega⟩ (certE ⟨629, by omega⟩) := by
  have hm : certMode (⟨629, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨629, by omega⟩ : Fin 1104) = 181074363497701099069655569994 := by decide +kernel
  have he : certE (⟨629, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨629, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨629, by omega⟩ : Fin 1104)).2.2 = 18138867453 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_630 :
    ((certNum ⟨630, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨630, by omega⟩) ⟨630, by omega⟩ (certE ⟨630, by omega⟩) := by
  have hm : certMode (⟨630, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨630, by omega⟩ : Fin 1104) = 203304065681780201378406535607 := by decide +kernel
  have he : certE (⟨630, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨630, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨630, by omega⟩ : Fin 1104)).2.2 = 20992527710 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_631 :
    ((certNum ⟨631, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨631, by omega⟩) ⟨631, by omega⟩ (certE ⟨631, by omega⟩) := by
  have hm : certMode (⟨631, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨631, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨631, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨631, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨631, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_632 :
    ((certNum ⟨632, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨632, by omega⟩) ⟨632, by omega⟩ (certE ⟨632, by omega⟩) := by
  have hm : certMode (⟨632, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨632, by omega⟩ : Fin 1104) = 190498059294622485034203532553 := by decide +kernel
  have he : certE (⟨632, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 13 else if j.val = 1 then 5 else if j.val = 2 then -3 else -7)) := by decide +kernel
  have hp : parent2 (⟨632, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨632, by omega⟩ : Fin 1104)).2.2 = 19335000475 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_633 :
    ((certNum ⟨633, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨633, by omega⟩) ⟨633, by omega⟩ (certE ⟨633, by omega⟩) := by
  have hm : certMode (⟨633, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨633, by omega⟩ : Fin 1104) = 203304059438718853172436494082 := by decide +kernel
  have he : certE (⟨633, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨633, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨633, by omega⟩ : Fin 1104)).2.2 = 20992526893 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_634 :
    ((certNum ⟨634, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨634, by omega⟩) ⟨634, by omega⟩ (certE ⟨634, by omega⟩) := by
  have hm : certMode (⟨634, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨634, by omega⟩ : Fin 1104) = 91299419867088758382478868417 := by decide +kernel
  have he : certE (⟨634, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -54 else if j.val = 1 then 7 else if j.val = 2 then 7 else 7)) := by decide +kernel
  have hp : parent2 (⟨634, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨634, by omega⟩ : Fin 1104)).2.2 = 7810862219 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_635 :
    ((certNum ⟨635, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨635, by omega⟩) ⟨635, by omega⟩ (certE ⟨635, by omega⟩) := by
  have hm : certMode (⟨635, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨635, by omega⟩ : Fin 1104) = 180786258274195413944655451799 := by decide +kernel
  have he : certE (⟨635, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hp : parent2 (⟨635, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨635, by omega⟩ : Fin 1104)).2.2 = 18102617206 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_636 :
    ((certNum ⟨636, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨636, by omega⟩) ⟨636, by omega⟩ (certE ⟨636, by omega⟩) := by
  have hm : certMode (⟨636, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨636, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨636, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨636, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨636, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_637 :
    ((certNum ⟨637, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨637, by omega⟩) ⟨637, by omega⟩ (certE ⟨637, by omega⟩) := by
  have hm : certMode (⟨637, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨637, by omega⟩ : Fin 1104) = 177446643422557414952858754761 := by decide +kernel
  have he : certE (⟨637, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 17 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨637, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨637, by omega⟩ : Fin 1104)).2.2 = 17683794889 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_638 :
    ((certNum ⟨638, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨638, by omega⟩) ⟨638, by omega⟩ (certE ⟨638, by omega⟩) := by
  have hm : certMode (⟨638, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨638, by omega⟩ : Fin 1104) = 203776709463748765263939642730 := by decide +kernel
  have he : certE (⟨638, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hp : parent2 (⟨638, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨638, by omega⟩ : Fin 1104)).2.2 = 21054405342 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_639 :
    ((certNum ⟨639, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨639, by omega⟩) ⟨639, by omega⟩ (certE ⟨639, by omega⟩) := by
  have hm : certMode (⟨639, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨639, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨639, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨639, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨639, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_640 :
    ((certNum ⟨640, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨640, by omega⟩) ⟨640, by omega⟩ (certE ⟨640, by omega⟩) := by
  have hm : certMode (⟨640, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨640, by omega⟩ : Fin 1104) = 203946187110964891497207539429 := by decide +kernel
  have he : certE (⟨640, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨640, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨640, by omega⟩ : Fin 1104)).2.2 = 21076605642 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_641 :
    ((certNum ⟨641, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨641, by omega⟩) ⟨641, by omega⟩ (certE ⟨641, by omega⟩) := by
  have hm : certMode (⟨641, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨641, by omega⟩ : Fin 1104) = 3046946591127616971998809 := by decide +kernel
  have he : certE (⟨641, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -30 else if j.val = 1 then 2 else if j.val = 2 then -7 else 7)) := by decide +kernel
  have hp : parent2 (⟨641, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨641, by omega⟩ : Fin 1104)).2.2 = 88359 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_642 :
    ((certNum ⟨642, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨642, by omega⟩) ⟨642, by omega⟩ (certE ⟨642, by omega⟩) := by
  have hm : certMode (⟨642, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨642, by omega⟩ : Fin 1104) = 3407240520322210580042971 := by decide +kernel
  have he : certE (⟨642, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -44 else if j.val = 1 then 6 else if j.val = 2 then 0 else 4)) := by decide +kernel
  have hp : parent2 (⟨642, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨642, by omega⟩ : Fin 1104)).2.2 = 99492 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_643 :
    ((certNum ⟨643, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨643, by omega⟩) ⟨643, by omega⟩ (certE ⟨643, by omega⟩) := by
  have hm : certMode (⟨643, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨643, by omega⟩ : Fin 1104) = 203946188988641241358683217387 := by decide +kernel
  have he : certE (⟨643, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨643, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨643, by omega⟩ : Fin 1104)).2.2 = 21076605888 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨552 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨552 + j.val, by omega⟩) ⟨552 + j.val, by omega⟩
        (certE ⟨552 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_552
  | ⟨1, _⟩ => exact MME.L2Cert.cert_553
  | ⟨2, _⟩ => exact MME.L2Cert.cert_554
  | ⟨3, _⟩ => exact MME.L2Cert.cert_555
  | ⟨4, _⟩ => exact MME.L2Cert.cert_556
  | ⟨5, _⟩ => exact MME.L2Cert.cert_557
  | ⟨6, _⟩ => exact MME.L2Cert.cert_558
  | ⟨7, _⟩ => exact MME.L2Cert.cert_559
  | ⟨8, _⟩ => exact MME.L2Cert.cert_560
  | ⟨9, _⟩ => exact MME.L2Cert.cert_561
  | ⟨10, _⟩ => exact MME.L2Cert.cert_562
  | ⟨11, _⟩ => exact MME.L2Cert.cert_563
  | ⟨12, _⟩ => exact MME.L2Cert.cert_564
  | ⟨13, _⟩ => exact MME.L2Cert.cert_565
  | ⟨14, _⟩ => exact MME.L2Cert.cert_566
  | ⟨15, _⟩ => exact MME.L2Cert.cert_567
  | ⟨16, _⟩ => exact MME.L2Cert.cert_568
  | ⟨17, _⟩ => exact MME.L2Cert.cert_569
  | ⟨18, _⟩ => exact MME.L2Cert.cert_570
  | ⟨19, _⟩ => exact MME.L2Cert.cert_571
  | ⟨20, _⟩ => exact MME.L2Cert.cert_572
  | ⟨21, _⟩ => exact MME.L2Cert.cert_573
  | ⟨22, _⟩ => exact MME.L2Cert.cert_574
  | ⟨23, _⟩ => exact MME.L2Cert.cert_575
  | ⟨24, _⟩ => exact MME.L2Cert.cert_576
  | ⟨25, _⟩ => exact MME.L2Cert.cert_577
  | ⟨26, _⟩ => exact MME.L2Cert.cert_578
  | ⟨27, _⟩ => exact MME.L2Cert.cert_579
  | ⟨28, _⟩ => exact MME.L2Cert.cert_580
  | ⟨29, _⟩ => exact MME.L2Cert.cert_581
  | ⟨30, _⟩ => exact MME.L2Cert.cert_582
  | ⟨31, _⟩ => exact MME.L2Cert.cert_583
  | ⟨32, _⟩ => exact MME.L2Cert.cert_584
  | ⟨33, _⟩ => exact MME.L2Cert.cert_585
  | ⟨34, _⟩ => exact MME.L2Cert.cert_586
  | ⟨35, _⟩ => exact MME.L2Cert.cert_587
  | ⟨36, _⟩ => exact MME.L2Cert.cert_588
  | ⟨37, _⟩ => exact MME.L2Cert.cert_589
  | ⟨38, _⟩ => exact MME.L2Cert.cert_590
  | ⟨39, _⟩ => exact MME.L2Cert.cert_591
  | ⟨40, _⟩ => exact MME.L2Cert.cert_592
  | ⟨41, _⟩ => exact MME.L2Cert.cert_593
  | ⟨42, _⟩ => exact MME.L2Cert.cert_594
  | ⟨43, _⟩ => exact MME.L2Cert.cert_595
  | ⟨44, _⟩ => exact MME.L2Cert.cert_596
  | ⟨45, _⟩ => exact MME.L2Cert.cert_597
  | ⟨46, _⟩ => exact MME.L2Cert.cert_598
  | ⟨47, _⟩ => exact MME.L2Cert.cert_599
  | ⟨48, _⟩ => exact MME.L2Cert.cert_600
  | ⟨49, _⟩ => exact MME.L2Cert.cert_601
  | ⟨50, _⟩ => exact MME.L2Cert.cert_602
  | ⟨51, _⟩ => exact MME.L2Cert.cert_603
  | ⟨52, _⟩ => exact MME.L2Cert.cert_604
  | ⟨53, _⟩ => exact MME.L2Cert.cert_605
  | ⟨54, _⟩ => exact MME.L2Cert.cert_606
  | ⟨55, _⟩ => exact MME.L2Cert.cert_607
  | ⟨56, _⟩ => exact MME.L2Cert.cert_608
  | ⟨57, _⟩ => exact MME.L2Cert.cert_609
  | ⟨58, _⟩ => exact MME.L2Cert.cert_610
  | ⟨59, _⟩ => exact MME.L2Cert.cert_611
  | ⟨60, _⟩ => exact MME.L2Cert.cert_612
  | ⟨61, _⟩ => exact MME.L2Cert.cert_613
  | ⟨62, _⟩ => exact MME.L2Cert.cert_614
  | ⟨63, _⟩ => exact MME.L2Cert.cert_615
  | ⟨64, _⟩ => exact MME.L2Cert.cert_616
  | ⟨65, _⟩ => exact MME.L2Cert.cert_617
  | ⟨66, _⟩ => exact MME.L2Cert.cert_618
  | ⟨67, _⟩ => exact MME.L2Cert.cert_619
  | ⟨68, _⟩ => exact MME.L2Cert.cert_620
  | ⟨69, _⟩ => exact MME.L2Cert.cert_621
  | ⟨70, _⟩ => exact MME.L2Cert.cert_622
  | ⟨71, _⟩ => exact MME.L2Cert.cert_623
  | ⟨72, _⟩ => exact MME.L2Cert.cert_624
  | ⟨73, _⟩ => exact MME.L2Cert.cert_625
  | ⟨74, _⟩ => exact MME.L2Cert.cert_626
  | ⟨75, _⟩ => exact MME.L2Cert.cert_627
  | ⟨76, _⟩ => exact MME.L2Cert.cert_628
  | ⟨77, _⟩ => exact MME.L2Cert.cert_629
  | ⟨78, _⟩ => exact MME.L2Cert.cert_630
  | ⟨79, _⟩ => exact MME.L2Cert.cert_631
  | ⟨80, _⟩ => exact MME.L2Cert.cert_632
  | ⟨81, _⟩ => exact MME.L2Cert.cert_633
  | ⟨82, _⟩ => exact MME.L2Cert.cert_634
  | ⟨83, _⟩ => exact MME.L2Cert.cert_635
  | ⟨84, _⟩ => exact MME.L2Cert.cert_636
  | ⟨85, _⟩ => exact MME.L2Cert.cert_637
  | ⟨86, _⟩ => exact MME.L2Cert.cert_638
  | ⟨87, _⟩ => exact MME.L2Cert.cert_639
  | ⟨88, _⟩ => exact MME.L2Cert.cert_640
  | ⟨89, _⟩ => exact MME.L2Cert.cert_641
  | ⟨90, _⟩ => exact MME.L2Cert.cert_642
  | ⟨91, _⟩ => exact MME.L2Cert.cert_643
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
