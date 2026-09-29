-- Prove2me | solution 1 for mme_released_recursive_level2_cert5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:26:56.039948+00:00
-- url     : https://prove2.me/submissions/4b21c8ce-0902-48a7-8855-976fc88a905f

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

theorem cert_460 :
    ((certNum ⟨460, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨460, by omega⟩) ⟨460, by omega⟩ (certE ⟨460, by omega⟩) := by
  have hm : certMode (⟨460, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨460, by omega⟩ : Fin 1104) = 5069947780502252852264153831 := by decide +kernel
  have he : certE (⟨460, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -10 else if j.val = 1 then -5 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hp : parent2 (⟨460, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨460, by omega⟩ : Fin 1104)).2.2 = 275658398 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_461 :
    ((certNum ⟨461, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨461, by omega⟩) ⟨461, by omega⟩ (certE ⟨461, by omega⟩) := by
  have hm : certMode (⟨461, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨461, by omega⟩ : Fin 1104) = 203306046269097326559793480632 := by decide +kernel
  have he : certE (⟨461, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨461, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨461, by omega⟩ : Fin 1104)).2.2 = 20992786901 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_462 :
    ((certNum ⟨462, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨462, by omega⟩) ⟨462, by omega⟩ (certE ⟨462, by omega⟩) := by
  have hm : certMode (⟨462, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨462, by omega⟩ : Fin 1104) = 10584925704118898024986875222 := by decide +kernel
  have he : certE (⟨462, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -6 else if j.val = 1 then -2 else if j.val = 2 then 3 else -3)) := by decide +kernel
  have hp : parent2 (⟨462, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨462, by omega⟩ : Fin 1104)).2.2 = 632700452 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_463 :
    ((certNum ⟨463, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨463, by omega⟩) ⟨463, by omega⟩ (certE ⟨463, by omega⟩) := by
  have hm : certMode (⟨463, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨463, by omega⟩ : Fin 1104) = 203306209030751274983358195241 := by decide +kernel
  have he : certE (⟨463, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨463, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨463, by omega⟩ : Fin 1104)).2.2 = 20992808201 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_464 :
    ((certNum ⟨464, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨464, by omega⟩) ⟨464, by omega⟩ (certE ⟨464, by omega⟩) := by
  have hm : certMode (⟨464, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨464, by omega⟩ : Fin 1104) = 5070856476752900790281938397 := by decide +kernel
  have he : certE (⟨464, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -10 else if j.val = 1 then -5 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hp : parent2 (⟨464, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨464, by omega⟩ : Fin 1104)).2.2 = 275713835 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_465 :
    ((certNum ⟨465, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨465, by omega⟩) ⟨465, by omega⟩ (certE ⟨465, by omega⟩) := by
  have hm : certMode (⟨465, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨465, by omega⟩ : Fin 1104) = 203306203421970898430114420576 := by decide +kernel
  have he : certE (⟨465, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨465, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨465, by omega⟩ : Fin 1104)).2.2 = 20992807467 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_466 :
    ((certNum ⟨466, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨466, by omega⟩) ⟨466, by omega⟩ (certE ⟨466, by omega⟩) := by
  have hm : certMode (⟨466, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨466, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨466, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨466, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨466, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_467 :
    ((certNum ⟨467, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨467, by omega⟩) ⟨467, by omega⟩ (certE ⟨467, by omega⟩) := by
  have hm : certMode (⟨467, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨467, by omega⟩ : Fin 1104) = 190862815010784835275552309191 := by decide +kernel
  have he : certE (⟨467, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hp : parent2 (⟨467, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨467, by omega⟩ : Fin 1104)).2.2 = 19381702428 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_468 :
    ((certNum ⟨468, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨468, by omega⟩) ⟨468, by omega⟩ (certE ⟨468, by omega⟩) := by
  have hm : certMode (⟨468, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨468, by omega⟩ : Fin 1104) = 203306194466261410163747170535 := by decide +kernel
  have he : certE (⟨468, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨468, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨468, by omega⟩ : Fin 1104)).2.2 = 20992806295 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_469 :
    ((certNum ⟨469, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨469, by omega⟩) ⟨469, by omega⟩ (certE ⟨469, by omega⟩) := by
  have hm : certMode (⟨469, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨469, by omega⟩ : Fin 1104) = 89359790595102530965881119579 := by decide +kernel
  have he : certE (⟨469, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then -30 else if j.val = 1 then -2 else if j.val = 2 then 4 else 6)) := by decide +kernel
  have hp : parent2 (⟨469, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨469, by omega⟩ : Fin 1104)).2.2 = 7610884407 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_470 :
    ((certNum ⟨470, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨470, by omega⟩) ⟨470, by omega⟩ (certE ⟨470, by omega⟩) := by
  have hm : certMode (⟨470, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨470, by omega⟩ : Fin 1104) = 181584778260160985608313618327 := by decide +kernel
  have he : certE (⟨470, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 9 else if j.val = 1 then -2 else if j.val = 2 then -5 else 0)) := by decide +kernel
  have hp : parent2 (⟨470, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨470, by omega⟩ : Fin 1104)).2.2 = 18203136667 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_471 :
    ((certNum ⟨471, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨471, by omega⟩) ⟨471, by omega⟩ (certE ⟨471, by omega⟩) := by
  have hm : certMode (⟨471, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨471, by omega⟩ : Fin 1104) = 203306190699055886791267510035 := by decide +kernel
  have he : certE (⟨471, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨471, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨471, by omega⟩ : Fin 1104)).2.2 = 20992805802 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_472 :
    ((certNum ⟨472, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨472, by omega⟩) ⟨472, by omega⟩ (certE ⟨472, by omega⟩) := by
  have hm : certMode (⟨472, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨472, by omega⟩ : Fin 1104) = 202769363079550905724147398463 := by decide +kernel
  have he : certE (⟨472, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨472, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨472, by omega⟩ : Fin 1104)).2.2 = 20922584697 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_473 :
    ((certNum ⟨473, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨473, by omega⟩) ⟨473, by omega⟩ (certE ⟨473, by omega⟩) := by
  have hm : certMode (⟨473, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨473, by omega⟩ : Fin 1104) = 181359296962149416117899611541 := by decide +kernel
  have he : certE (⟨473, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then -3 else 6)) := by decide +kernel
  have hp : parent2 (⟨473, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨473, by omega⟩ : Fin 1104)).2.2 = 18174737873 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_474 :
    ((certNum ⟨474, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨474, by omega⟩) ⟨474, by omega⟩ (certE ⟨474, by omega⟩) := by
  have hm : certMode (⟨474, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨474, by omega⟩ : Fin 1104) = 90551423557796100373701323489 := by decide +kernel
  have he : certE (⟨474, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then 14 else if j.val = 1 then 5 else if j.val = 2 then -4 else -7)) := by decide +kernel
  have hp : parent2 (⟨474, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨474, by omega⟩ : Fin 1104)).2.2 = 7733614430 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_475 :
    ((certNum ⟨475, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨475, by omega⟩) ⟨475, by omega⟩ (certE ⟨475, by omega⟩) := by
  have hm : certMode (⟨475, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨475, by omega⟩ : Fin 1104) = 202769370988015894175857693215 := by decide +kernel
  have he : certE (⟨475, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨475, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨475, by omega⟩ : Fin 1104)).2.2 = 20922585731 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_476 :
    ((certNum ⟨476, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨476, by omega⟩) ⟨476, by omega⟩ (certE ⟨476, by omega⟩) := by
  have hm : certMode (⟨476, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨476, by omega⟩ : Fin 1104) = 190819364439639040537618834930 := by decide +kernel
  have he : certE (⟨476, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨476, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨476, by omega⟩ : Fin 1104)).2.2 = 19376137542 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_477 :
    ((certNum ⟨477, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨477, by omega⟩) ⟨477, by omega⟩ (certE ⟨477, by omega⟩) := by
  have hm : certMode (⟨477, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨477, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨477, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨477, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨477, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_478 :
    ((certNum ⟨478, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨478, by omega⟩) ⟨478, by omega⟩ (certE ⟨478, by omega⟩) := by
  have hm : certMode (⟨478, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨478, by omega⟩ : Fin 1104) = 180783551255876225799107100577 := by decide +kernel
  have he : certE (⟨478, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hp : parent2 (⟨478, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨478, by omega⟩ : Fin 1104)).2.2 = 18102276687 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_479 :
    ((certNum ⟨479, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨479, by omega⟩) ⟨479, by omega⟩ (certE ⟨479, by omega⟩) := by
  have hm : certMode (⟨479, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨479, by omega⟩ : Fin 1104) = 91301730236458024108642263133 := by decide +kernel
  have he : certE (⟨479, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -3 else if j.val = 1 then -6 else if j.val = 2 then 6 else -3)) := by decide +kernel
  have hp : parent2 (⟨479, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨479, by omega⟩ : Fin 1104)).2.2 = 7811101067 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_480 :
    ((certNum ⟨480, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨480, by omega⟩) ⟨480, by omega⟩ (certE ⟨480, by omega⟩) := by
  have hm : certMode (⟨480, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨480, by omega⟩ : Fin 1104) = 203306197530458970600274025318 := by decide +kernel
  have he : certE (⟨480, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨480, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨480, by omega⟩ : Fin 1104)).2.2 = 20992806696 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_481 :
    ((certNum ⟨481, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨481, by omega⟩) ⟨481, by omega⟩ (certE ⟨481, by omega⟩) := by
  have hm : certMode (⟨481, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨481, by omega⟩ : Fin 1104) = 190495618873931056682080393542 := by decide +kernel
  have he : certE (⟨481, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 13 else if j.val = 1 then 5 else if j.val = 2 then -3 else -7)) := by decide +kernel
  have hp : parent2 (⟨481, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨481, by omega⟩ : Fin 1104)).2.2 = 19334688127 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_482 :
    ((certNum ⟨482, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨482, by omega⟩) ⟨482, by omega⟩ (certE ⟨482, by omega⟩) := by
  have hm : certMode (⟨482, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨482, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨482, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨482, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨482, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_483 :
    ((certNum ⟨483, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨483, by omega⟩) ⟨483, by omega⟩ (certE ⟨483, by omega⟩) := by
  have hm : certMode (⟨483, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨483, by omega⟩ : Fin 1104) = 203306202619624922995615634773 := by decide +kernel
  have he : certE (⟨483, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨483, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨483, by omega⟩ : Fin 1104)).2.2 = 20992807362 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_484 :
    ((certNum ⟨484, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨484, by omega⟩) ⟨484, by omega⟩ (certE ⟨484, by omega⟩) := by
  have hm : certMode (⟨484, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨484, by omega⟩ : Fin 1104) = 181069906019117382486702653621 := by decide +kernel
  have he : certE (⟨484, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨484, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨484, by omega⟩ : Fin 1104)).2.2 = 18138306440 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_485 :
    ((certNum ⟨485, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨485, by omega⟩) ⟨485, by omega⟩ (certE ⟨485, by omega⟩) := by
  have hm : certMode (⟨485, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨485, by omega⟩ : Fin 1104) = 203946148473573274309499224506 := by decide +kernel
  have he : certE (⟨485, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨485, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨485, by omega⟩ : Fin 1104)).2.2 = 21076600580 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_486 :
    ((certNum ⟨486, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨486, by omega⟩) ⟨486, by omega⟩ (certE ⟨486, by omega⟩) := by
  have hm : certMode (⟨486, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨486, by omega⟩ : Fin 1104) = 89928069038374986251040476282 := by decide +kernel
  have he : certE (⟨486, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -29 else if j.val = 1 then 0 else if j.val = 2 then 1 else 7)) := by decide +kernel
  have hp : parent2 (⟨486, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨486, by omega⟩ : Fin 1104)).2.2 = 7669362099 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_487 :
    ((certNum ⟨487, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨487, by omega⟩) ⟨487, by omega⟩ (certE ⟨487, by omega⟩) := by
  have hm : certMode (⟨487, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨487, by omega⟩ : Fin 1104) = 190580790315494494984289903025 := by decide +kernel
  have he : certE (⟨487, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -5 else -3)) := by decide +kernel
  have hp : parent2 (⟨487, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨487, by omega⟩ : Fin 1104)).2.2 = 19345590324 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_488 :
    ((certNum ⟨488, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨488, by omega⟩) ⟨488, by omega⟩ (certE ⟨488, by omega⟩) := by
  have hm : certMode (⟨488, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨488, by omega⟩ : Fin 1104) = 203946142145955712131712868186 := by decide +kernel
  have he : certE (⟨488, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨488, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨488, by omega⟩ : Fin 1104)).2.2 = 21076599751 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_489 :
    ((certNum ⟨489, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨489, by omega⟩) ⟨489, by omega⟩ (certE ⟨489, by omega⟩) := by
  have hm : certMode (⟨489, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨489, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨489, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨489, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨489, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_490 :
    ((certNum ⟨490, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨490, by omega⟩) ⟨490, by omega⟩ (certE ⟨490, by omega⟩) := by
  have hm : certMode (⟨490, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨490, by omega⟩ : Fin 1104) = 25358913453687981762787131708 := by decide +kernel
  have he : certE (⟨490, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -7 else if j.val = 1 then -4 else if j.val = 2 then 3 else -1)) := by decide +kernel
  have hp : parent2 (⟨490, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨490, by omega⟩ : Fin 1104)).2.2 = 1722181650 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_491 :
    ((certNum ⟨491, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨491, by omega⟩) ⟨491, by omega⟩ (certE ⟨491, by omega⟩) := by
  have hm : certMode (⟨491, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨491, by omega⟩ : Fin 1104) = 203306207945673880795364505543 := by decide +kernel
  have he : certE (⟨491, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨491, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨491, by omega⟩ : Fin 1104)).2.2 = 20992808059 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_492 :
    ((certNum ⟨492, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨492, by omega⟩) ⟨492, by omega⟩ (certE ⟨492, by omega⟩) := by
  have hm : certMode (⟨492, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨492, by omega⟩ : Fin 1104) = 15739331684992077751936294175 := by decide +kernel
  have he : certE (⟨492, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 12 else if j.val = 1 then 0 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨492, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨492, by omega⟩ : Fin 1104)).2.2 = 994631394 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_493 :
    ((certNum ⟨493, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨493, by omega⟩) ⟨493, by omega⟩ (certE ⟨493, by omega⟩) := by
  have hm : certMode (⟨493, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨493, by omega⟩ : Fin 1104) = 203306201939541189719686894875 := by decide +kernel
  have he : certE (⟨493, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨493, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨493, by omega⟩ : Fin 1104)).2.2 = 20992807273 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_494 :
    ((certNum ⟨494, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨494, by omega⟩) ⟨494, by omega⟩ (certE ⟨494, by omega⟩) := by
  have hm : certMode (⟨494, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨494, by omega⟩ : Fin 1104) = 15740422157706687188172570089 := by decide +kernel
  have he : certE (⟨494, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 12 else if j.val = 1 then 0 else if j.val = 2 then -1 else -7)) := by decide +kernel
  have hp : parent2 (⟨494, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨494, by omega⟩ : Fin 1104)).2.2 = 994710286 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_495 :
    ((certNum ⟨495, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨495, by omega⟩) ⟨495, by omega⟩ (certE ⟨495, by omega⟩) := by
  have hm : certMode (⟨495, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨495, by omega⟩ : Fin 1104) = 203306208656323160540710545835 := by decide +kernel
  have he : certE (⟨495, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨495, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨495, by omega⟩ : Fin 1104)).2.2 = 20992808152 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_496 :
    ((certNum ⟨496, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨496, by omega⟩) ⟨496, by omega⟩ (certE ⟨496, by omega⟩) := by
  have hm : certMode (⟨496, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨496, by omega⟩ : Fin 1104) = 202769517585219464355969854356 := by decide +kernel
  have he : certE (⟨496, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨496, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨496, by omega⟩ : Fin 1104)).2.2 = 20922604898 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_497 :
    ((certNum ⟨497, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨497, by omega⟩) ⟨497, by omega⟩ (certE ⟨497, by omega⟩) := by
  have hm : certMode (⟨497, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨497, by omega⟩ : Fin 1104) = 10619605201096347383244268975 := by decide +kernel
  have he : certE (⟨497, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -4 else if j.val = 1 then 4 else if j.val = 2 then -8 else 2)) := by decide +kernel
  have hp : parent2 (⟨497, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨497, by omega⟩ : Fin 1104)).2.2 = 635055615 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_498 :
    ((certNum ⟨498, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨498, by omega⟩) ⟨498, by omega⟩ (certE ⟨498, by omega⟩) := by
  have hm : certMode (⟨498, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨498, by omega⟩ : Fin 1104) = 202769420220882596013942909917 := by decide +kernel
  have he : certE (⟨498, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨498, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨498, by omega⟩ : Fin 1104)).2.2 = 20922592168 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_499 :
    ((certNum ⟨499, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨499, by omega⟩) ⟨499, by omega⟩ (certE ⟨499, by omega⟩) := by
  have hm : certMode (⟨499, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨499, by omega⟩ : Fin 1104) = 18687613576782853244121628886 := by decide +kernel
  have he : certE (⟨499, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -13 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨499, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨499, by omega⟩ : Fin 1104)).2.2 = 1211122869 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_500 :
    ((certNum ⟨500, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨500, by omega⟩) ⟨500, by omega⟩ (certE ⟨500, by omega⟩) := by
  have hm : certMode (⟨500, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨500, by omega⟩ : Fin 1104) = 202769644434151867329325862089 := by decide +kernel
  have he : certE (⟨500, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨500, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨500, by omega⟩ : Fin 1104)).2.2 = 20922621483 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_501 :
    ((certNum ⟨501, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨501, by omega⟩) ⟨501, by omega⟩ (certE ⟨501, by omega⟩) := by
  have hm : certMode (⟨501, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨501, by omega⟩ : Fin 1104) = 10620184501342040995123716120 := by decide +kernel
  have he : certE (⟨501, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -4 else if j.val = 1 then 4 else if j.val = 2 then -8 else 2)) := by decide +kernel
  have hp : parent2 (⟨501, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨501, by omega⟩ : Fin 1104)).2.2 = 635094967 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_502 :
    ((certNum ⟨502, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨502, by omega⟩) ⟨502, by omega⟩ (certE ⟨502, by omega⟩) := by
  have hm : certMode (⟨502, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨502, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨502, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨502, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨502, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_503 :
    ((certNum ⟨503, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨503, by omega⟩) ⟨503, by omega⟩ (certE ⟨503, by omega⟩) := by
  have hm : certMode (⟨503, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨503, by omega⟩ : Fin 1104) = 3996916554094101847665929 := by decide +kernel
  have he : certE (⟨503, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -34 else if j.val = 1 then 4 else if j.val = 2 then 2 else 0)) := by decide +kernel
  have hp : parent2 (⟨503, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨503, by omega⟩ : Fin 1104)).2.2 = 117878 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_504 :
    ((certNum ⟨504, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨504, by omega⟩) ⟨504, by omega⟩ (certE ⟨504, by omega⟩) := by
  have hm : certMode (⟨504, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨504, by omega⟩ : Fin 1104) = 196709636618045739161672213072 := by decide +kernel
  have he : certE (⟨504, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -32 else if j.val = 1 then 1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨504, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨504, by omega⟩ : Fin 1104)).2.2 = 20134395205 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_505 :
    ((certNum ⟨505, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨505, by omega⟩) ⟨505, by omega⟩ (certE ⟨505, by omega⟩) := by
  have hm : certMode (⟨505, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨505, by omega⟩ : Fin 1104) = 3948589478459596114878751 := by decide +kernel
  have he : certE (⟨505, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -25 else if j.val = 1 then 1 else if j.val = 2 then 5 else -4)) := by decide +kernel
  have hp : parent2 (⟨505, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨505, by omega⟩ : Fin 1104)).2.2 = 116364 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_506 :
    ((certNum ⟨506, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨506, by omega⟩) ⟨506, by omega⟩ (certE ⟨506, by omega⟩) := by
  have hm : certMode (⟨506, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨506, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨506, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨506, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨506, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_507 :
    ((certNum ⟨507, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨507, by omega⟩) ⟨507, by omega⟩ (certE ⟨507, by omega⟩) := by
  have hm : certMode (⟨507, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨507, by omega⟩ : Fin 1104) = 196709636958088264145258228843 := by decide +kernel
  have he : certE (⟨507, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -32 else if j.val = 1 then 1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hp : parent2 (⟨507, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨507, by omega⟩ : Fin 1104)).2.2 = 20134395249 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_508 :
    ((certNum ⟨508, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨508, by omega⟩) ⟨508, by omega⟩ (certE ⟨508, by omega⟩) := by
  have hm : certMode (⟨508, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨508, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨508, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨508, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨508, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_509 :
    ((certNum ⟨509, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨509, by omega⟩) ⟨509, by omega⟩ (certE ⟨509, by omega⟩) := by
  have hm : certMode (⟨509, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨509, by omega⟩ : Fin 1104) = 203946081068028647933887537417 := by decide +kernel
  have he : certE (⟨509, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨509, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨509, by omega⟩ : Fin 1104)).2.2 = 21076591749 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_510 :
    ((certNum ⟨510, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨510, by omega⟩) ⟨510, by omega⟩ (certE ⟨510, by omega⟩) := by
  have hm : certMode (⟨510, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨510, by omega⟩ : Fin 1104) = 169605996174727314680601514793 := by decide +kernel
  have he : certE (⟨510, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 14 else if j.val = 1 then 1 else if j.val = 2 then -2 else -6)) := by decide +kernel
  have hp : parent2 (⟨510, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨510, by omega⟩ : Fin 1104)).2.2 = 16710561351 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_511 :
    ((certNum ⟨511, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨511, by omega⟩) ⟨511, by omega⟩ (certE ⟨511, by omega⟩) := by
  have hm : certMode (⟨511, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨511, by omega⟩ : Fin 1104) = 203866922891444034975552889651 := by decide +kernel
  have he : certE (⟨511, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨511, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨511, by omega⟩ : Fin 1104)).2.2 = 21066221783 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_512 :
    ((certNum ⟨512, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨512, by omega⟩) ⟨512, by omega⟩ (certE ⟨512, by omega⟩) := by
  have hm : certMode (⟨512, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨512, by omega⟩ : Fin 1104) = 203946053979101423565117545803 := by decide +kernel
  have he : certE (⟨512, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨512, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨512, by omega⟩ : Fin 1104)).2.2 = 21076588200 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_513 :
    ((certNum ⟨513, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨513, by omega⟩) ⟨513, by omega⟩ (certE ⟨513, by omega⟩) := by
  have hm : certMode (⟨513, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨513, by omega⟩ : Fin 1104) = 53342979466743677088426607526 := by decide +kernel
  have he : certE (⟨513, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 16 else if j.val = 1 then -6 else if j.val = 2 then -5 else -1)) := by decide +kernel
  have hp : parent2 (⟨513, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨513, by omega⟩ : Fin 1104)).2.2 = 4109402777 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_514 :
    ((certNum ⟨514, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨514, by omega⟩) ⟨514, by omega⟩ (certE ⟨514, by omega⟩) := by
  have hm : certMode (⟨514, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨514, by omega⟩ : Fin 1104) = 203776057644330396372579595061 := by decide +kernel
  have he : certE (⟨514, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨514, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨514, by omega⟩ : Fin 1104)).2.2 = 21054319970 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_515 :
    ((certNum ⟨515, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨515, by omega⟩) ⟨515, by omega⟩ (certE ⟨515, by omega⟩) := by
  have hm : certMode (⟨515, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨515, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨515, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨515, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨515, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_516 :
    ((certNum ⟨516, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨516, by omega⟩) ⟨516, by omega⟩ (certE ⟨516, by omega⟩) := by
  have hm : certMode (⟨516, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨516, by omega⟩ : Fin 1104) = 169654817026394572063806086083 := by decide +kernel
  have he : certE (⟨516, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 13 else if j.val = 1 then -6 else if j.val = 2 then 2 else -5)) := by decide +kernel
  have hp : parent2 (⟨516, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨516, by omega⟩ : Fin 1104)).2.2 = 16716577455 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_517 :
    ((certNum ⟨517, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨517, by omega⟩) ⟨517, by omega⟩ (certE ⟨517, by omega⟩) := by
  have hm : certMode (⟨517, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨517, by omega⟩ : Fin 1104) = 203776116739158558874788676595 := by decide +kernel
  have he : certE (⟨517, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨517, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨517, by omega⟩ : Fin 1104)).2.2 = 21054327710 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_518 :
    ((certNum ⟨518, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨518, by omega⟩) ⟨518, by omega⟩ (certE ⟨518, by omega⟩) := by
  have hm : certMode (⟨518, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨518, by omega⟩ : Fin 1104) = 204037716837331645225609152340 := by decide +kernel
  have he : certE (⟨518, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -3 else if j.val = 1 then -7 else if j.val = 2 then -6 else 8)) := by decide +kernel
  have hp : parent2 (⟨518, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨518, by omega⟩ : Fin 1104)).2.2 = 21088598141 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_519 :
    ((certNum ⟨519, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨519, by omega⟩) ⟨519, by omega⟩ (certE ⟨519, by omega⟩) := by
  have hm : certMode (⟨519, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨519, by omega⟩ : Fin 1104) = 53341635991918418371030987545 := by decide +kernel
  have he : certE (⟨519, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 16 else if j.val = 1 then -6 else if j.val = 2 then -5 else -1)) := by decide +kernel
  have hp : parent2 (⟨519, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨519, by omega⟩ : Fin 1104)).2.2 = 4109280337 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_520 :
    ((certNum ⟨520, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨520, by omega⟩) ⟨520, by omega⟩ (certE ⟨520, by omega⟩) := by
  have hm : certMode (⟨520, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨520, by omega⟩ : Fin 1104) = 203946065237531609965222261636 := by decide +kernel
  have he : certE (⟨520, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨520, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨520, by omega⟩ : Fin 1104)).2.2 = 21076589675 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_521 :
    ((certNum ⟨521, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨521, by omega⟩) ⟨521, by omega⟩ (certE ⟨521, by omega⟩) := by
  have hm : certMode (⟨521, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨521, by omega⟩ : Fin 1104) = 18364692507634285886397413323 := by decide +kernel
  have he : certE (⟨521, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -19 else if j.val = 1 then 8 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hp : parent2 (⟨521, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨521, by omega⟩ : Fin 1104)).2.2 = 1187109476 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_522 :
    ((certNum ⟨522, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨522, by omega⟩) ⟨522, by omega⟩ (certE ⟨522, by omega⟩) := by
  have hm : certMode (⟨522, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨522, by omega⟩ : Fin 1104) = 203946071717807501445210601944 := by decide +kernel
  have he : certE (⟨522, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨522, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨522, by omega⟩ : Fin 1104)).2.2 = 21076590524 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_523 :
    ((certNum ⟨523, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨523, by omega⟩) ⟨523, by omega⟩ (certE ⟨523, by omega⟩) := by
  have hm : certMode (⟨523, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨523, by omega⟩ : Fin 1104) = 10401768152392037773579948374 := by decide +kernel
  have he : certE (⟨523, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -12 else if j.val = 1 then -3 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hp : parent2 (⟨523, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨523, by omega⟩ : Fin 1104)).2.2 = 620281658 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_524 :
    ((certNum ⟨524, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨524, by omega⟩) ⟨524, by omega⟩ (certE ⟨524, by omega⟩) := by
  have hm : certMode (⟨524, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨524, by omega⟩ : Fin 1104) = 203946043537384092502061344631 := by decide +kernel
  have he : certE (⟨524, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨524, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨524, by omega⟩ : Fin 1104)).2.2 = 21076586832 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_525 :
    ((certNum ⟨525, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨525, by omega⟩) ⟨525, by omega⟩ (certE ⟨525, by omega⟩) := by
  have hm : certMode (⟨525, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨525, by omega⟩ : Fin 1104) = 10402548845741988353524232252 := by decide +kernel
  have he : certE (⟨525, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -12 else if j.val = 1 then -3 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hp : parent2 (⟨525, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨525, by omega⟩ : Fin 1104)).2.2 = 620334521 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_526 :
    ((certNum ⟨526, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨526, by omega⟩) ⟨526, by omega⟩ (certE ⟨526, by omega⟩) := by
  have hm : certMode (⟨526, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨526, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨526, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨526, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨526, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_527 :
    ((certNum ⟨527, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨527, by omega⟩) ⟨527, by omega⟩ (certE ⟨527, by omega⟩) := by
  have hm : certMode (⟨527, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨527, by omega⟩ : Fin 1104) = 180699340007610315459241769141 := by decide +kernel
  have he : certE (⟨527, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -13 else if j.val = 1 then -4 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨527, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨527, by omega⟩ : Fin 1104)).2.2 = 18091684220 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_528 :
    ((certNum ⟨528, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨528, by omega⟩) ⟨528, by omega⟩ (certE ⟨528, by omega⟩) := by
  have hm : certMode (⟨528, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨528, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨528, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨528, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨528, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_529 :
    ((certNum ⟨529, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨529, by omega⟩) ⟨529, by omega⟩ (certE ⟨529, by omega⟩) := by
  have hm : certMode (⟨529, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨529, by omega⟩ : Fin 1104) = 180693211009306089116033422070 := by decide +kernel
  have he : certE (⟨529, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -13 else if j.val = 1 then 7 else if j.val = 2 then 8 else -8)) := by decide +kernel
  have hp : parent2 (⟨529, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨529, by omega⟩ : Fin 1104)).2.2 = 18090913362 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_530 :
    ((certNum ⟨530, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨530, by omega⟩) ⟨530, by omega⟩ (certE ⟨530, by omega⟩) := by
  have hm : certMode (⟨530, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨530, by omega⟩ : Fin 1104) = 203775278110665787342731251548 := by decide +kernel
  have he : certE (⟨530, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨530, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨530, by omega⟩ : Fin 1104)).2.2 = 21054217870 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_531 :
    ((certNum ⟨531, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨531, by omega⟩) ⟨531, by omega⟩ (certE ⟨531, by omega⟩) := by
  have hm : certMode (⟨531, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨531, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨531, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨531, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨531, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_532 :
    ((certNum ⟨532, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨532, by omega⟩) ⟨532, by omega⟩ (certE ⟨532, by omega⟩) := by
  have hm : certMode (⟨532, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨532, by omega⟩ : Fin 1104) = 203775029109922485344877985377 := by decide +kernel
  have he : certE (⟨532, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨532, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨532, by omega⟩ : Fin 1104)).2.2 = 21054185257 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_533 :
    ((certNum ⟨533, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨533, by omega⟩) ⟨533, by omega⟩ (certE ⟨533, by omega⟩) := by
  have hm : certMode (⟨533, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨533, by omega⟩ : Fin 1104) = 166404339993766791169734773 := by decide +kernel
  have he : certE (⟨533, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -39 else if j.val = 1 then -6 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨533, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨533, by omega⟩ : Fin 1104)).2.2 = 6422019 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_534 :
    ((certNum ⟨534, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨534, by omega⟩) ⟨534, by omega⟩ (certE ⟨534, by omega⟩) := by
  have hm : certMode (⟨534, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨534, by omega⟩ : Fin 1104) = 203775155087695901097406193543 := by decide +kernel
  have he : certE (⟨534, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨534, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨534, by omega⟩ : Fin 1104)).2.2 = 21054201757 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_535 :
    ((certNum ⟨535, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨535, by omega⟩) ⟨535, by omega⟩ (certE ⟨535, by omega⟩) := by
  have hm : certMode (⟨535, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨535, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨535, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨535, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨535, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_536 :
    ((certNum ⟨536, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨536, by omega⟩) ⟨536, by omega⟩ (certE ⟨536, by omega⟩) := by
  have hm : certMode (⟨536, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨536, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨536, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨536, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨536, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_537 :
    ((certNum ⟨537, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨537, by omega⟩) ⟨537, by omega⟩ (certE ⟨537, by omega⟩) := by
  have hm : certMode (⟨537, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨537, by omega⟩ : Fin 1104) = 180696650932219748683512701513 := by decide +kernel
  have he : certE (⟨537, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -13 else if j.val = 1 then -4 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hp : parent2 (⟨537, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨537, by omega⟩ : Fin 1104)).2.2 = 18091346007 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_538 :
    ((certNum ⟨538, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨538, by omega⟩) ⟨538, by omega⟩ (certE ⟨538, by omega⟩) := by
  have hm : certMode (⟨538, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨538, by omega⟩ : Fin 1104) = 203942087717996836019651875455 := by decide +kernel
  have he : certE (⟨538, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨538, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨538, by omega⟩ : Fin 1104)).2.2 = 21076068572 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_539 :
    ((certNum ⟨539, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨539, by omega⟩) ⟨539, by omega⟩ (certE ⟨539, by omega⟩) := by
  have hm : certMode (⟨539, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨539, by omega⟩ : Fin 1104) = 160754962348855403083272972 := by decide +kernel
  have he : certE (⟨539, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -30 else if j.val = 1 then 6 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨539, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨539, by omega⟩ : Fin 1104)).2.2 = 6186124 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_540 :
    ((certNum ⟨540, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨540, by omega⟩) ⟨540, by omega⟩ (certE ⟨540, by omega⟩) := by
  have hm : certMode (⟨540, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨540, by omega⟩ : Fin 1104) = 203943964979460735940997753810 := by decide +kernel
  have he : certE (⟨540, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨540, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨540, by omega⟩ : Fin 1104)).2.2 = 21076314515 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_541 :
    ((certNum ⟨541, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨541, by omega⟩) ⟨541, by omega⟩ (certE ⟨541, by omega⟩) := by
  have hm : certMode (⟨541, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨541, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨541, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨541, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨541, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_542 :
    ((certNum ⟨542, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨542, by omega⟩) ⟨542, by omega⟩ (certE ⟨542, by omega⟩) := by
  have hm : certMode (⟨542, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨542, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨542, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨542, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨542, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_543 :
    ((certNum ⟨543, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨543, by omega⟩) ⟨543, by omega⟩ (certE ⟨543, by omega⟩) := by
  have hm : certMode (⟨543, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨543, by omega⟩ : Fin 1104) = 180692001048732930621020083924 := by decide +kernel
  have he : certE (⟨543, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -13 else if j.val = 1 then 7 else if j.val = 2 then 8 else -8)) := by decide +kernel
  have hp : parent2 (⟨543, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨543, by omega⟩ : Fin 1104)).2.2 = 18090761180 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_544 :
    ((certNum ⟨544, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨544, by omega⟩) ⟨544, by omega⟩ (certE ⟨544, by omega⟩) := by
  have hm : certMode (⟨544, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨544, by omega⟩ : Fin 1104) = 203944423112698401260045293657 := by decide +kernel
  have he : certE (⟨544, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨544, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨544, by omega⟩ : Fin 1104)).2.2 = 21076374536 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_545 :
    ((certNum ⟨545, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨545, by omega⟩) ⟨545, by omega⟩ (certE ⟨545, by omega⟩) := by
  have hm : certMode (⟨545, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨545, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨545, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨545, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨545, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_546 :
    ((certNum ⟨546, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨546, by omega⟩) ⟨546, by omega⟩ (certE ⟨546, by omega⟩) := by
  have hm : certMode (⟨546, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨546, by omega⟩ : Fin 1104) = 179721938865467669740719769908 := by decide +kernel
  have he : certE (⟨546, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨546, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨546, by omega⟩ : Fin 1104)).2.2 = 17968863418 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_547 :
    ((certNum ⟨547, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨547, by omega⟩) ⟨547, by omega⟩ (certE ⟨547, by omega⟩) := by
  have hm : certMode (⟨547, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨547, by omega⟩ : Fin 1104) = 179721862306590955666694858111 := by decide +kernel
  have he : certE (⟨547, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨547, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨547, by omega⟩ : Fin 1104)).2.2 = 17968853806 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_548 :
    ((certNum ⟨548, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨548, by omega⟩) ⟨548, by omega⟩ (certE ⟨548, by omega⟩) := by
  have hm : certMode (⟨548, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨548, by omega⟩ : Fin 1104) = 179722274682460758941455633917 := by decide +kernel
  have he : certE (⟨548, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨548, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨548, by omega⟩ : Fin 1104)).2.2 = 17968905580 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_549 :
    ((certNum ⟨549, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨549, by omega⟩) ⟨549, by omega⟩ (certE ⟨549, by omega⟩) := by
  have hm : certMode (⟨549, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨549, by omega⟩ : Fin 1104) = 179723253337909995054277745261 := by decide +kernel
  have he : certE (⟨549, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨549, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨549, by omega⟩ : Fin 1104)).2.2 = 17969028451 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_550 :
    ((certNum ⟨550, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨550, by omega⟩) ⟨550, by omega⟩ (certE ⟨550, by omega⟩) := by
  have hm : certMode (⟨550, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨550, by omega⟩ : Fin 1104) = 179722275208145213597937231459 := by decide +kernel
  have he : certE (⟨550, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨550, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨550, by omega⟩ : Fin 1104)).2.2 = 17968905646 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_551 :
    ((certNum ⟨551, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨551, by omega⟩) ⟨551, by omega⟩ (certE ⟨551, by omega⟩) := by
  have hm : certMode (⟨551, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨551, by omega⟩ : Fin 1104) = 179723252621070108726257472719 := by decide +kernel
  have he : certE (⟨551, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (2 : Int) else if j.val = 1 then -3 else if j.val = 2 then 6 else -4) else (if j.val = 0 then -29 else if j.val = 1 then 2 else if j.val = 2 then 5 else 3)) := by decide +kernel
  have hp : parent2 (⟨551, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨551, by omega⟩ : Fin 1104)).2.2 = 17969028361 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨460 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨460 + j.val, by omega⟩) ⟨460 + j.val, by omega⟩
        (certE ⟨460 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_460
  | ⟨1, _⟩ => exact MME.L2Cert.cert_461
  | ⟨2, _⟩ => exact MME.L2Cert.cert_462
  | ⟨3, _⟩ => exact MME.L2Cert.cert_463
  | ⟨4, _⟩ => exact MME.L2Cert.cert_464
  | ⟨5, _⟩ => exact MME.L2Cert.cert_465
  | ⟨6, _⟩ => exact MME.L2Cert.cert_466
  | ⟨7, _⟩ => exact MME.L2Cert.cert_467
  | ⟨8, _⟩ => exact MME.L2Cert.cert_468
  | ⟨9, _⟩ => exact MME.L2Cert.cert_469
  | ⟨10, _⟩ => exact MME.L2Cert.cert_470
  | ⟨11, _⟩ => exact MME.L2Cert.cert_471
  | ⟨12, _⟩ => exact MME.L2Cert.cert_472
  | ⟨13, _⟩ => exact MME.L2Cert.cert_473
  | ⟨14, _⟩ => exact MME.L2Cert.cert_474
  | ⟨15, _⟩ => exact MME.L2Cert.cert_475
  | ⟨16, _⟩ => exact MME.L2Cert.cert_476
  | ⟨17, _⟩ => exact MME.L2Cert.cert_477
  | ⟨18, _⟩ => exact MME.L2Cert.cert_478
  | ⟨19, _⟩ => exact MME.L2Cert.cert_479
  | ⟨20, _⟩ => exact MME.L2Cert.cert_480
  | ⟨21, _⟩ => exact MME.L2Cert.cert_481
  | ⟨22, _⟩ => exact MME.L2Cert.cert_482
  | ⟨23, _⟩ => exact MME.L2Cert.cert_483
  | ⟨24, _⟩ => exact MME.L2Cert.cert_484
  | ⟨25, _⟩ => exact MME.L2Cert.cert_485
  | ⟨26, _⟩ => exact MME.L2Cert.cert_486
  | ⟨27, _⟩ => exact MME.L2Cert.cert_487
  | ⟨28, _⟩ => exact MME.L2Cert.cert_488
  | ⟨29, _⟩ => exact MME.L2Cert.cert_489
  | ⟨30, _⟩ => exact MME.L2Cert.cert_490
  | ⟨31, _⟩ => exact MME.L2Cert.cert_491
  | ⟨32, _⟩ => exact MME.L2Cert.cert_492
  | ⟨33, _⟩ => exact MME.L2Cert.cert_493
  | ⟨34, _⟩ => exact MME.L2Cert.cert_494
  | ⟨35, _⟩ => exact MME.L2Cert.cert_495
  | ⟨36, _⟩ => exact MME.L2Cert.cert_496
  | ⟨37, _⟩ => exact MME.L2Cert.cert_497
  | ⟨38, _⟩ => exact MME.L2Cert.cert_498
  | ⟨39, _⟩ => exact MME.L2Cert.cert_499
  | ⟨40, _⟩ => exact MME.L2Cert.cert_500
  | ⟨41, _⟩ => exact MME.L2Cert.cert_501
  | ⟨42, _⟩ => exact MME.L2Cert.cert_502
  | ⟨43, _⟩ => exact MME.L2Cert.cert_503
  | ⟨44, _⟩ => exact MME.L2Cert.cert_504
  | ⟨45, _⟩ => exact MME.L2Cert.cert_505
  | ⟨46, _⟩ => exact MME.L2Cert.cert_506
  | ⟨47, _⟩ => exact MME.L2Cert.cert_507
  | ⟨48, _⟩ => exact MME.L2Cert.cert_508
  | ⟨49, _⟩ => exact MME.L2Cert.cert_509
  | ⟨50, _⟩ => exact MME.L2Cert.cert_510
  | ⟨51, _⟩ => exact MME.L2Cert.cert_511
  | ⟨52, _⟩ => exact MME.L2Cert.cert_512
  | ⟨53, _⟩ => exact MME.L2Cert.cert_513
  | ⟨54, _⟩ => exact MME.L2Cert.cert_514
  | ⟨55, _⟩ => exact MME.L2Cert.cert_515
  | ⟨56, _⟩ => exact MME.L2Cert.cert_516
  | ⟨57, _⟩ => exact MME.L2Cert.cert_517
  | ⟨58, _⟩ => exact MME.L2Cert.cert_518
  | ⟨59, _⟩ => exact MME.L2Cert.cert_519
  | ⟨60, _⟩ => exact MME.L2Cert.cert_520
  | ⟨61, _⟩ => exact MME.L2Cert.cert_521
  | ⟨62, _⟩ => exact MME.L2Cert.cert_522
  | ⟨63, _⟩ => exact MME.L2Cert.cert_523
  | ⟨64, _⟩ => exact MME.L2Cert.cert_524
  | ⟨65, _⟩ => exact MME.L2Cert.cert_525
  | ⟨66, _⟩ => exact MME.L2Cert.cert_526
  | ⟨67, _⟩ => exact MME.L2Cert.cert_527
  | ⟨68, _⟩ => exact MME.L2Cert.cert_528
  | ⟨69, _⟩ => exact MME.L2Cert.cert_529
  | ⟨70, _⟩ => exact MME.L2Cert.cert_530
  | ⟨71, _⟩ => exact MME.L2Cert.cert_531
  | ⟨72, _⟩ => exact MME.L2Cert.cert_532
  | ⟨73, _⟩ => exact MME.L2Cert.cert_533
  | ⟨74, _⟩ => exact MME.L2Cert.cert_534
  | ⟨75, _⟩ => exact MME.L2Cert.cert_535
  | ⟨76, _⟩ => exact MME.L2Cert.cert_536
  | ⟨77, _⟩ => exact MME.L2Cert.cert_537
  | ⟨78, _⟩ => exact MME.L2Cert.cert_538
  | ⟨79, _⟩ => exact MME.L2Cert.cert_539
  | ⟨80, _⟩ => exact MME.L2Cert.cert_540
  | ⟨81, _⟩ => exact MME.L2Cert.cert_541
  | ⟨82, _⟩ => exact MME.L2Cert.cert_542
  | ⟨83, _⟩ => exact MME.L2Cert.cert_543
  | ⟨84, _⟩ => exact MME.L2Cert.cert_544
  | ⟨85, _⟩ => exact MME.L2Cert.cert_545
  | ⟨86, _⟩ => exact MME.L2Cert.cert_546
  | ⟨87, _⟩ => exact MME.L2Cert.cert_547
  | ⟨88, _⟩ => exact MME.L2Cert.cert_548
  | ⟨89, _⟩ => exact MME.L2Cert.cert_549
  | ⟨90, _⟩ => exact MME.L2Cert.cert_550
  | ⟨91, _⟩ => exact MME.L2Cert.cert_551
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
