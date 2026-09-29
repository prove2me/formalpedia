-- Prove2me | solution 1 for mme_released_recursive_level2_cert9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T00:53:28.733313+00:00
-- url     : https://prove2.me/submissions/a29fa1f3-b794-4d98-8420-ecdfb96400b3

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

theorem cert_828 :
    ((certNum ⟨828, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨828, by omega⟩) ⟨828, by omega⟩ (certE ⟨828, by omega⟩) := by
  have hm : certMode (⟨828, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨828, by omega⟩ : Fin 1104) = 15742154204348359897003028403 := by decide +kernel
  have he : certE (⟨828, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 8 else if j.val = 1 then 6 else if j.val = 2 then -7 else -4)) := by decide +kernel
  have hp : parent2 (⟨828, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨828, by omega⟩ : Fin 1104)).2.2 = 994835597 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_829 :
    ((certNum ⟨829, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨829, by omega⟩) ⟨829, by omega⟩ (certE ⟨829, by omega⟩) := by
  have hm : certMode (⟨829, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨829, by omega⟩ : Fin 1104) = 203306475417130191111134865033 := by decide +kernel
  have he : certE (⟨829, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨829, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨829, by omega⟩ : Fin 1104)).2.2 = 20992843062 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_830 :
    ((certNum ⟨830, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨830, by omega⟩) ⟨830, by omega⟩ (certE ⟨830, by omega⟩) := by
  have hm : certMode (⟨830, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨830, by omega⟩ : Fin 1104) = 25361203874044530935611786407 := by decide +kernel
  have he : certE (⟨830, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -7 else if j.val = 1 then -4 else if j.val = 2 then 3 else -1)) := by decide +kernel
  have hp : parent2 (⟨830, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨830, by omega⟩ : Fin 1104)).2.2 = 1722361693 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_831 :
    ((certNum ⟨831, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨831, by omega⟩) ⟨831, by omega⟩ (certE ⟨831, by omega⟩) := by
  have hm : certMode (⟨831, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨831, by omega⟩ : Fin 1104) = 203306479841491002604729955615 := by decide +kernel
  have he : certE (⟨831, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨831, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨831, by omega⟩ : Fin 1104)).2.2 = 20992843641 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_832 :
    ((certNum ⟨832, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨832, by omega⟩) ⟨832, by omega⟩ (certE ⟨832, by omega⟩) := by
  have hm : certMode (⟨832, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨832, by omega⟩ : Fin 1104) = 15742589113490725962986959640 := by decide +kernel
  have he : certE (⟨832, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then 8 else if j.val = 1 then 6 else if j.val = 2 then -7 else -4)) := by decide +kernel
  have hp : parent2 (⟨832, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨832, by omega⟩ : Fin 1104)).2.2 = 994867062 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_833 :
    ((certNum ⟨833, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨833, by omega⟩) ⟨833, by omega⟩ (certE ⟨833, by omega⟩) := by
  have hm : certMode (⟨833, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨833, by omega⟩ : Fin 1104) = 203306480934208774795254515019 := by decide +kernel
  have he : certE (⟨833, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨833, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨833, by omega⟩ : Fin 1104)).2.2 = 20992843784 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_834 :
    ((certNum ⟨834, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨834, by omega⟩) ⟨834, by omega⟩ (certE ⟨834, by omega⟩) := by
  have hm : certMode (⟨834, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨834, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨834, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨834, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨834, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_835 :
    ((certNum ⟨835, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨835, by omega⟩) ⟨835, by omega⟩ (certE ⟨835, by omega⟩) := by
  have hm : certMode (⟨835, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨835, by omega⟩ : Fin 1104) = 190494582214403170962524520570 := by decide +kernel
  have he : certE (⟨835, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 18 else if j.val = 1 then -5 else if j.val = 2 then -8 else 1)) := by decide +kernel
  have hp : parent2 (⟨835, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨835, by omega⟩ : Fin 1104)).2.2 = 19334555441 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_836 :
    ((certNum ⟨836, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨836, by omega⟩) ⟨836, by omega⟩ (certE ⟨836, by omega⟩) := by
  have hm : certMode (⟨836, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨836, by omega⟩ : Fin 1104) = 203306475501185405767804150795 := by decide +kernel
  have he : certE (⟨836, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨836, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨836, by omega⟩ : Fin 1104)).2.2 = 20992843073 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_837 :
    ((certNum ⟨837, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨837, by omega⟩) ⟨837, by omega⟩ (certE ⟨837, by omega⟩) := by
  have hm : certMode (⟨837, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨837, by omega⟩ : Fin 1104) = 91294328528885958791943554626 := by decide +kernel
  have he : certE (⟨837, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -6 else if j.val = 1 then 7 else if j.val = 2 then -4 else -1)) := by decide +kernel
  have hp : parent2 (⟨837, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨837, by omega⟩ : Fin 1104)).2.2 = 7810335879 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_838 :
    ((certNum ⟨838, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨838, by omega⟩) ⟨838, by omega⟩ (certE ⟨838, by omega⟩) := by
  have hm : certMode (⟨838, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨838, by omega⟩ : Fin 1104) = 180787224416659243509539041860 := by decide +kernel
  have he : certE (⟨838, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hp : parent2 (⟨838, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨838, by omega⟩ : Fin 1104)).2.2 = 18102738739 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_839 :
    ((certNum ⟨839, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨839, by omega⟩) ⟨839, by omega⟩ (certE ⟨839, by omega⟩) := by
  have hm : certMode (⟨839, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨839, by omega⟩ : Fin 1104) = 203306470190424068818250040328 := by decide +kernel
  have he : certE (⟨839, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨839, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨839, by omega⟩ : Fin 1104)).2.2 = 20992842378 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_840 :
    ((certNum ⟨840, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨840, by omega⟩) ⟨840, by omega⟩ (certE ⟨840, by omega⟩) := by
  have hm : certMode (⟨840, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨840, by omega⟩ : Fin 1104) = 203947316790639077207357153493 := by decide +kernel
  have he : certE (⟨840, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨840, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨840, by omega⟩ : Fin 1104)).2.2 = 21076753645 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_841 :
    ((certNum ⟨841, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨841, by omega⟩) ⟨841, by omega⟩ (certE ⟨841, by omega⟩) := by
  have hm : certMode (⟨841, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨841, by omega⟩ : Fin 1104) = 181066110805240832018790453305 := by decide +kernel
  have he : certE (⟨841, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hp : parent2 (⟨841, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨841, by omega⟩ : Fin 1104)).2.2 = 18137828786 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_842 :
    ((certNum ⟨842, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨842, by omega⟩) ⟨842, by omega⟩ (certE ⟨842, by omega⟩) := by
  have hm : certMode (⟨842, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨842, by omega⟩ : Fin 1104) = 89929810673540137517074849267 := by decide +kernel
  have he : certE (⟨842, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -29 else if j.val = 1 then 0 else if j.val = 2 then 1 else 7)) := by decide +kernel
  have hp : parent2 (⟨842, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨842, by omega⟩ : Fin 1104)).2.2 = 7669541458 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_843 :
    ((certNum ⟨843, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨843, by omega⟩) ⟨843, by omega⟩ (certE ⟨843, by omega⟩) := by
  have hm : certMode (⟨843, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨843, by omega⟩ : Fin 1104) = 203947319958251636869212499535 := by decide +kernel
  have he : certE (⟨843, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨843, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨843, by omega⟩ : Fin 1104)).2.2 = 21076754060 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_844 :
    ((certNum ⟨844, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨844, by omega⟩) ⟨844, by omega⟩ (certE ⟨844, by omega⟩) := by
  have hm : certMode (⟨844, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨844, by omega⟩ : Fin 1104) = 190579728598494382781182268287 := by decide +kernel
  have he : certE (⟨844, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -5 else -3)) := by decide +kernel
  have hp : parent2 (⟨844, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨844, by omega⟩ : Fin 1104)).2.2 = 19345454410 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_845 :
    ((certNum ⟨845, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨845, by omega⟩) ⟨845, by omega⟩ (certE ⟨845, by omega⟩) := by
  have hm : certMode (⟨845, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨845, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨845, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨845, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨845, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_846 :
    ((certNum ⟨846, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨846, by omega⟩) ⟨846, by omega⟩ (certE ⟨846, by omega⟩) := by
  have hm : certMode (⟨846, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨846, by omega⟩ : Fin 1104) = 181581829696051216274446142986 := by decide +kernel
  have he : certE (⟨846, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then 9 else if j.val = 1 then -2 else if j.val = 2 then -5 else 0)) := by decide +kernel
  have hp : parent2 (⟨846, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨846, by omega⟩ : Fin 1104)).2.2 = 18202765233 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_847 :
    ((certNum ⟨847, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨847, by omega⟩) ⟨847, by omega⟩ (certE ⟨847, by omega⟩) := by
  have hm : certMode (⟨847, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨847, by omega⟩ : Fin 1104) = 89374959649837662541154385728 := by decide +kernel
  have he : certE (⟨847, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 8 else if j.val = 1 then 7 else if j.val = 2 then -4 else -6)) := by decide +kernel
  have hp : parent2 (⟨847, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨847, by omega⟩ : Fin 1104)).2.2 = 7612444124 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_848 :
    ((certNum ⟨848, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨848, by omega⟩) ⟨848, by omega⟩ (certE ⟨848, by omega⟩) := by
  have hm : certMode (⟨848, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨848, by omega⟩ : Fin 1104) = 203306464482310697371148189916 := by decide +kernel
  have he : certE (⟨848, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨848, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨848, by omega⟩ : Fin 1104)).2.2 = 20992841631 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_849 :
    ((certNum ⟨849, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨849, by omega⟩) ⟨849, by omega⟩ (certE ⟨849, by omega⟩) := by
  have hm : certMode (⟨849, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨849, by omega⟩ : Fin 1104) = 190863105973556289469538482059 := by decide +kernel
  have he : certE (⟨849, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -13 else if j.val = 1 then 4 else if j.val = 2 then -2 else 2)) := by decide +kernel
  have hp : parent2 (⟨849, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨849, by omega⟩ : Fin 1104)).2.2 = 19381739695 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_850 :
    ((certNum ⟨850, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨850, by omega⟩) ⟨850, by omega⟩ (certE ⟨850, by omega⟩) := by
  have hm : certMode (⟨850, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨850, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨850, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨850, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨850, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_851 :
    ((certNum ⟨851, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨851, by omega⟩) ⟨851, by omega⟩ (certE ⟨851, by omega⟩) := by
  have hm : certMode (⟨851, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨851, by omega⟩ : Fin 1104) = 203306467875084923498493432822 := by decide +kernel
  have he : certE (⟨851, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨851, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨851, by omega⟩ : Fin 1104)).2.2 = 20992842075 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_852 :
    ((certNum ⟨852, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨852, by omega⟩) ⟨852, by omega⟩ (certE ⟨852, by omega⟩) := by
  have hm : certMode (⟨852, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨852, by omega⟩ : Fin 1104) = 181365397368437262557494922167 := by decide +kernel
  have he : certE (⟨852, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then -3 else 6)) := by decide +kernel
  have hp : parent2 (⟨852, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨852, by omega⟩ : Fin 1104)).2.2 = 18175506034 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_853 :
    ((certNum ⟨853, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨853, by omega⟩) ⟨853, by omega⟩ (certE ⟨853, by omega⟩) := by
  have hm : certMode (⟨853, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨853, by omega⟩ : Fin 1104) = 202780334225173966725274230998 := by decide +kernel
  have he : certE (⟨853, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨853, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨853, by omega⟩ : Fin 1104)).2.2 = 20924019157 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_854 :
    ((certNum ⟨854, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨854, by omega⟩) ⟨854, by omega⟩ (certE ⟨854, by omega⟩) := by
  have hm : certMode (⟨854, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨854, by omega⟩ : Fin 1104) = 90531094973300466899773611142 := by decide +kernel
  have he : certE (⟨854, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-10 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else 4) else (if j.val = 0 then -28 else if j.val = 1 then 2 else if j.val = 2 then -2 else 8)) := by decide +kernel
  have hp : parent2 (⟨854, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨854, by omega⟩ : Fin 1104)).2.2 = 7731517250 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_855 :
    ((certNum ⟨855, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨855, by omega⟩) ⟨855, by omega⟩ (certE ⟨855, by omega⟩) := by
  have hm : certMode (⟨855, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨855, by omega⟩ : Fin 1104) = 190817539686958170360661880424 := by decide +kernel
  have he : certE (⟨855, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -9 else if j.val = 1 then -2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hp : parent2 (⟨855, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨855, by omega⟩ : Fin 1104)).2.2 = 19375903850 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_856 :
    ((certNum ⟨856, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨856, by omega⟩) ⟨856, by omega⟩ (certE ⟨856, by omega⟩) := by
  have hm : certMode (⟨856, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨856, by omega⟩ : Fin 1104) = 202780321888735770164667578234 := by decide +kernel
  have he : certE (⟨856, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨856, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨856, by omega⟩ : Fin 1104)).2.2 = 20924017544 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_857 :
    ((certNum ⟨857, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨857, by omega⟩) ⟨857, by omega⟩ (certE ⟨857, by omega⟩) := by
  have hm : certMode (⟨857, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨857, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨857, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨857, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨857, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_858 :
    ((certNum ⟨858, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨858, by omega⟩) ⟨858, by omega⟩ (certE ⟨858, by omega⟩) := by
  have hm : certMode (⟨858, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨858, by omega⟩ : Fin 1104) = 10599499201567064947007084941 := by decide +kernel
  have he : certE (⟨858, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -26 else if j.val = 1 then 5 else if j.val = 2 then 2 else 1)) := by decide +kernel
  have hp : parent2 (⟨858, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨858, by omega⟩ : Fin 1104)).2.2 = 633690026 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_859 :
    ((certNum ⟨859, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨859, by omega⟩) ⟨859, by omega⟩ (certE ⟨859, by omega⟩) := by
  have hm : certMode (⟨859, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨859, by omega⟩ : Fin 1104) = 203306480873077710724173346237 := by decide +kernel
  have he : certE (⟨859, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨859, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨859, by omega⟩ : Fin 1104)).2.2 = 20992843776 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_860 :
    ((certNum ⟨860, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨860, by omega⟩) ⟨860, by omega⟩ (certE ⟨860, by omega⟩) := by
  have hm : certMode (⟨860, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨860, by omega⟩ : Fin 1104) = 5079300212303218314768776987 := by decide +kernel
  have he : certE (⟨860, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 12 else if j.val = 1 then 5 else if j.val = 2 then -4 else -8)) := by decide +kernel
  have hp : parent2 (⟨860, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨860, by omega⟩ : Fin 1104)).2.2 = 276229029 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_861 :
    ((certNum ⟨861, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨861, by omega⟩) ⟨861, by omega⟩ (certE ⟨861, by omega⟩) := by
  have hm : certMode (⟨861, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨861, by omega⟩ : Fin 1104) = 203306380556984419393050234132 := by decide +kernel
  have he : certE (⟨861, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨861, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨861, by omega⟩ : Fin 1104)).2.2 = 20992830648 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_862 :
    ((certNum ⟨862, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨862, by omega⟩) ⟨862, by omega⟩ (certE ⟨862, by omega⟩) := by
  have hm : certMode (⟨862, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨862, by omega⟩ : Fin 1104) = 5080389018962850542599855252 := by decide +kernel
  have he : certE (⟨862, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then 11 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hp : parent2 (⟨862, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨862, by omega⟩ : Fin 1104)).2.2 = 276295471 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_863 :
    ((certNum ⟨863, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨863, by omega⟩) ⟨863, by omega⟩ (certE ⟨863, by omega⟩) := by
  have hm : certMode (⟨863, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨863, by omega⟩ : Fin 1104) = 203306476899558518797960771905 := by decide +kernel
  have he : certE (⟨863, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hp : parent2 (⟨863, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨863, by omega⟩ : Fin 1104)).2.2 = 20992843256 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_864 :
    ((certNum ⟨864, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨864, by omega⟩) ⟨864, by omega⟩ (certE ⟨864, by omega⟩) := by
  have hm : certMode (⟨864, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨864, by omega⟩ : Fin 1104) = 203947305639116035394640490798 := by decide +kernel
  have he : certE (⟨864, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨864, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨864, by omega⟩ : Fin 1104)).2.2 = 21076752184 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_865 :
    ((certNum ⟨865, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨865, by omega⟩) ⟨865, by omega⟩ (certE ⟨865, by omega⟩) := by
  have hm : certMode (⟨865, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨865, by omega⟩ : Fin 1104) = 10394885125860373667813992805 := by decide +kernel
  have he : certE (⟨865, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -2 else if j.val = 1 then -1 else if j.val = 2 then 3 else -5)) := by decide +kernel
  have hp : parent2 (⟨865, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨865, by omega⟩ : Fin 1104)).2.2 = 619815616 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_866 :
    ((certNum ⟨866, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨866, by omega⟩) ⟨866, by omega⟩ (certE ⟨866, by omega⟩) := by
  have hm : certMode (⟨866, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨866, by omega⟩ : Fin 1104) = 203947340963720084720430237756 := by decide +kernel
  have he : certE (⟨866, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨866, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨866, by omega⟩ : Fin 1104)).2.2 = 21076756812 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_867 :
    ((certNum ⟨867, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨867, by omega⟩) ⟨867, by omega⟩ (certE ⟨867, by omega⟩) := by
  have hm : certMode (⟨867, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨867, by omega⟩ : Fin 1104) = 18356368925168942928290436042 := by decide +kernel
  have he : certE (⟨867, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -13 else if j.val = 1 then 5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hp : parent2 (⟨867, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨867, by omega⟩ : Fin 1104)).2.2 = 1186491461 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_868 :
    ((certNum ⟨868, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨868, by omega⟩) ⟨868, by omega⟩ (certE ⟨868, by omega⟩) := by
  have hm : certMode (⟨868, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨868, by omega⟩ : Fin 1104) = 203947233135123945744698165291 := by decide +kernel
  have he : certE (⟨868, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨868, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨868, by omega⟩ : Fin 1104)).2.2 = 21076742685 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_869 :
    ((certNum ⟨869, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨869, by omega⟩) ⟨869, by omega⟩ (certE ⟨869, by omega⟩) := by
  have hm : certMode (⟨869, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨869, by omega⟩ : Fin 1104) = 10395470525763816625340001041 := by decide +kernel
  have he : certE (⟨869, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -6 else if j.val = 1 then 5 else if j.val = 2 then -3 else -2)) := by decide +kernel
  have hp : parent2 (⟨869, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨869, by omega⟩ : Fin 1104)).2.2 = 619855251 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_870 :
    ((certNum ⟨870, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨870, by omega⟩) ⟨870, by omega⟩ (certE ⟨870, by omega⟩) := by
  have hm : certMode (⟨870, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨870, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨870, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨870, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨870, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_871 :
    ((certNum ⟨871, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨871, by omega⟩) ⟨871, by omega⟩ (certE ⟨871, by omega⟩) := by
  have hm : certMode (⟨871, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨871, by omega⟩ : Fin 1104) = 4075006830669957510227245 := by decide +kernel
  have he : certE (⟨871, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -38 else if j.val = 1 then 3 else if j.val = 2 then 2 else 2)) := by decide +kernel
  have hp : parent2 (⟨871, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨871, by omega⟩ : Fin 1104)).2.2 = 120327 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_872 :
    ((certNum ⟨872, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨872, by omega⟩) ⟨872, by omega⟩ (certE ⟨872, by omega⟩) := by
  have hm : certMode (⟨872, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨872, by omega⟩ : Fin 1104) = 196686183696942873007435593019 := by decide +kernel
  have he : certE (⟨872, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -28 else if j.val = 1 then -5 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hp : parent2 (⟨872, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨872, by omega⟩ : Fin 1104)).2.2 = 20131360620 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_873 :
    ((certNum ⟨873, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨873, by omega⟩) ⟨873, by omega⟩ (certE ⟨873, by omega⟩) := by
  have hm : certMode (⟨873, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨873, by omega⟩ : Fin 1104) = 3764781417623558202616157 := by decide +kernel
  have he : certE (⟨873, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -1 else if j.val = 1 then -4 else if j.val = 2 then -8 else 1)) := by decide +kernel
  have hp : parent2 (⟨873, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨873, by omega⟩ : Fin 1104)).2.2 = 110617 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_874 :
    ((certNum ⟨874, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨874, by omega⟩) ⟨874, by omega⟩ (certE ⟨874, by omega⟩) := by
  have hm : certMode (⟨874, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨874, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨874, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨874, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨874, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_875 :
    ((certNum ⟨875, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨875, by omega⟩) ⟨875, by omega⟩ (certE ⟨875, by omega⟩) := by
  have hm : certMode (⟨875, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨875, by omega⟩ : Fin 1104) = 196686183650571924371187803879 := by decide +kernel
  have he : certE (⟨875, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -28 else if j.val = 1 then -5 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hp : parent2 (⟨875, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨875, by omega⟩ : Fin 1104)).2.2 = 20131360614 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_876 :
    ((certNum ⟨876, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨876, by omega⟩) ⟨876, by omega⟩ (certE ⟨876, by omega⟩) := by
  have hm : certMode (⟨876, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨876, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨876, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨876, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨876, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_877 :
    ((certNum ⟨877, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨877, by omega⟩) ⟨877, by omega⟩ (certE ⟨877, by omega⟩) := by
  have hm : certMode (⟨877, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨877, by omega⟩ : Fin 1104) = 203774460140179910942438831593 := by decide +kernel
  have he : certE (⟨877, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨877, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨877, by omega⟩ : Fin 1104)).2.2 = 21054110736 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_878 :
    ((certNum ⟨878, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨878, by omega⟩) ⟨878, by omega⟩ (certE ⟨878, by omega⟩) := by
  have hm : certMode (⟨878, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨878, by omega⟩ : Fin 1104) = 169627356255509622328351060800 := by decide +kernel
  have he : certE (⟨878, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 10 else if j.val = 1 then 7 else if j.val = 2 then -8 else -3)) := by decide +kernel
  have hp : parent2 (⟨878, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨878, by omega⟩ : Fin 1104)).2.2 = 16713193449 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_879 :
    ((certNum ⟨879, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨879, by omega⟩) ⟨879, by omega⟩ (certE ⟨879, by omega⟩) := by
  have hm : certMode (⟨879, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨879, by omega⟩ : Fin 1104) = 204038936299665353748698238353 := by decide +kernel
  have he : certE (⟨879, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hp : parent2 (⟨879, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨879, by omega⟩ : Fin 1104)).2.2 = 21088757931 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_880 :
    ((certNum ⟨880, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨880, by omega⟩) ⟨880, by omega⟩ (certE ⟨880, by omega⟩) := by
  have hm : certMode (⟨880, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨880, by omega⟩ : Fin 1104) = 203774422003187658657144171060 := by decide +kernel
  have he : certE (⟨880, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨880, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨880, by omega⟩ : Fin 1104)).2.2 = 21054105741 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_881 :
    ((certNum ⟨881, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨881, by omega⟩) ⟨881, by omega⟩ (certE ⟨881, by omega⟩) := by
  have hm : certMode (⟨881, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨881, by omega⟩ : Fin 1104) = 53281032638460824547956759701 := by decide +kernel
  have he : certE (⟨881, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -16 else if j.val = 1 then 4 else if j.val = 2 then 8 else -6)) := by decide +kernel
  have hp : parent2 (⟨881, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨881, by omega⟩ : Fin 1104)).2.2 = 4103757767 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_882 :
    ((certNum ⟨882, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨882, by omega⟩) ⟨882, by omega⟩ (certE ⟨882, by omega⟩) := by
  have hm : certMode (⟨882, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨882, by omega⟩ : Fin 1104) = 203947218808351312149559983384 := by decide +kernel
  have he : certE (⟨882, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨882, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨882, by omega⟩ : Fin 1104)).2.2 = 21076740808 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_883 :
    ((certNum ⟨883, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨883, by omega⟩) ⟨883, by omega⟩ (certE ⟨883, by omega⟩) := by
  have hm : certMode (⟨883, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨883, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨883, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨883, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨883, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_884 :
    ((certNum ⟨884, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨884, by omega⟩) ⟨884, by omega⟩ (certE ⟨884, by omega⟩) := by
  have hm : certMode (⟨884, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨884, by omega⟩ : Fin 1104) = 169582495392941796646928734234 := by decide +kernel
  have he : certE (⟨884, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 15 else if j.val = 1 then 8 else if j.val = 2 then -6 else -7)) := by decide +kernel
  have hp : parent2 (⟨884, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨884, by omega⟩ : Fin 1104)).2.2 = 16707665595 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_885 :
    ((certNum ⟨885, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨885, by omega⟩) ⟨885, by omega⟩ (certE ⟨885, by omega⟩) := by
  have hm : certMode (⟨885, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨885, by omega⟩ : Fin 1104) = 203947270024461243454065497643 := by decide +kernel
  have he : certE (⟨885, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨885, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨885, by omega⟩ : Fin 1104)).2.2 = 21076747518 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_886 :
    ((certNum ⟨886, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨886, by omega⟩) ⟨886, by omega⟩ (certE ⟨886, by omega⟩) := by
  have hm : certMode (⟨886, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨886, by omega⟩ : Fin 1104) = 203865799834582256404446992573 := by decide +kernel
  have he : certE (⟨886, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hp : parent2 (⟨886, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨886, by omega⟩ : Fin 1104)).2.2 = 21066074669 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_887 :
    ((certNum ⟨887, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨887, by omega⟩) ⟨887, by omega⟩ (certE ⟨887, by omega⟩) := by
  have hm : certMode (⟨887, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨887, by omega⟩ : Fin 1104) = 53280717410942139048771338293 := by decide +kernel
  have he : certE (⟨887, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -16 else if j.val = 1 then 4 else if j.val = 2 then 8 else -6)) := by decide +kernel
  have hp : parent2 (⟨887, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨887, by omega⟩ : Fin 1104)).2.2 = 4103729045 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_888 :
    ((certNum ⟨888, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨888, by omega⟩) ⟨888, by omega⟩ (certE ⟨888, by omega⟩) := by
  have hm : certMode (⟨888, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨888, by omega⟩ : Fin 1104) = 202780303755011973430472081994 := by decide +kernel
  have he : certE (⟨888, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨888, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨888, by omega⟩ : Fin 1104)).2.2 = 20924015173 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_889 :
    ((certNum ⟨889, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨889, by omega⟩) ⟨889, by omega⟩ (certE ⟨889, by omega⟩) := by
  have hm : certMode (⟨889, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨889, by omega⟩ : Fin 1104) = 18673655928710587349467449320 := by decide +kernel
  have he : certE (⟨889, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -7 else if j.val = 1 then 6 else if j.val = 2 then 2 else -6)) := by decide +kernel
  have hp : parent2 (⟨889, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨889, by omega⟩ : Fin 1104)).2.2 = 1210083453 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_890 :
    ((certNum ⟨890, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨890, by omega⟩) ⟨890, by omega⟩ (certE ⟨890, by omega⟩) := by
  have hm : certMode (⟨890, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨890, by omega⟩ : Fin 1104) = 202780638704824097239634744901 := by decide +kernel
  have he : certE (⟨890, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨890, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨890, by omega⟩ : Fin 1104)).2.2 = 20924058968 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_891 :
    ((certNum ⟨891, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨891, by omega⟩) ⟨891, by omega⟩ (certE ⟨891, by omega⟩) := by
  have hm : certMode (⟨891, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨891, by omega⟩ : Fin 1104) = 10610167656381556524165908744 := by decide +kernel
  have he : certE (⟨891, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 6 else if j.val = 1 then 6 else if j.val = 2 then -4 else -6)) := by decide +kernel
  have hp : parent2 (⟨891, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨891, by omega⟩ : Fin 1104)).2.2 = 634414573 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_892 :
    ((certNum ⟨892, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨892, by omega⟩) ⟨892, by omega⟩ (certE ⟨892, by omega⟩) := by
  have hm : certMode (⟨892, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨892, by omega⟩ : Fin 1104) = 202780407379553473623953552664 := by decide +kernel
  have he : certE (⟨892, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hp : parent2 (⟨892, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨892, by omega⟩ : Fin 1104)).2.2 = 20924028722 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_893 :
    ((certNum ⟨893, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨893, by omega⟩) ⟨893, by omega⟩ (certE ⟨893, by omega⟩) := by
  have hm : certMode (⟨893, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨893, by omega⟩ : Fin 1104) = 10610963628404936123295336317 := by decide +kernel
  have he : certE (⟨893, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then 6 else if j.val = 1 then 6 else if j.val = 2 then -4 else -6)) := by decide +kernel
  have hp : parent2 (⟨893, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨893, by omega⟩ : Fin 1104)).2.2 = 634468635 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_894 :
    ((certNum ⟨894, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨894, by omega⟩) ⟨894, by omega⟩ (certE ⟨894, by omega⟩) := by
  have hm : certMode (⟨894, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨894, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨894, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨894, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨894, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_895 :
    ((certNum ⟨895, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨895, by omega⟩) ⟨895, by omega⟩ (certE ⟨895, by omega⟩) := by
  have hm : certMode (⟨895, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨895, by omega⟩ : Fin 1104) = 180563343851272225599108008456 := by decide +kernel
  have he : certE (⟨895, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then -6 else if j.val = 2 then -6 else 7)) := by decide +kernel
  have hp : parent2 (⟨895, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨895, by omega⟩ : Fin 1104)).2.2 = 18074581602 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_896 :
    ((certNum ⟨896, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨896, by omega⟩) ⟨896, by omega⟩ (certE ⟨896, by omega⟩) := by
  have hm : certMode (⟨896, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨896, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨896, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨896, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨896, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_897 :
    ((certNum ⟨897, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨897, by omega⟩) ⟨897, by omega⟩ (certE ⟨897, by omega⟩) := by
  have hm : certMode (⟨897, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨897, by omega⟩ : Fin 1104) = 180556703598751328386395460495 := by decide +kernel
  have he : certE (⟨897, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then 5 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hp : parent2 (⟨897, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨897, by omega⟩ : Fin 1104)).2.2 = 18073746653 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_898 :
    ((certNum ⟨898, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨898, by omega⟩) ⟨898, by omega⟩ (certE ⟨898, by omega⟩) := by
  have hm : certMode (⟨898, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨898, by omega⟩ : Fin 1104) = 203946023539357174776855143748 := by decide +kernel
  have he : certE (⟨898, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨898, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨898, by omega⟩ : Fin 1104)).2.2 = 21076584212 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_899 :
    ((certNum ⟨899, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨899, by omega⟩) ⟨899, by omega⟩ (certE ⟨899, by omega⟩) := by
  have hm : certMode (⟨899, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨899, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨899, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨899, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨899, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_900 :
    ((certNum ⟨900, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨900, by omega⟩) ⟨900, by omega⟩ (certE ⟨900, by omega⟩) := by
  have hm : certMode (⟨900, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨900, by omega⟩ : Fin 1104) = 203944705910636954842860630354 := by decide +kernel
  have he : certE (⟨900, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨900, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨900, by omega⟩ : Fin 1104)).2.2 = 21076411586 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_901 :
    ((certNum ⟨901, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨901, by omega⟩) ⟨901, by omega⟩ (certE ⟨901, by omega⟩) := by
  have hm : certMode (⟨901, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨901, by omega⟩ : Fin 1104) = 146906728982728367597820055 := by decide +kernel
  have he : certE (⟨901, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -26 else if j.val = 1 then -7 else if j.val = 2 then 0 else 7)) := by decide +kernel
  have hp : parent2 (⟨901, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨901, by omega⟩ : Fin 1104)).2.2 = 5611087 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_902 :
    ((certNum ⟨902, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨902, by omega⟩) ⟨902, by omega⟩ (certE ⟨902, by omega⟩) := by
  have hm : certMode (⟨902, by omega⟩ : Fin 1104) = 2 := by decide +kernel
  have hn : certNum (⟨902, by omega⟩ : Fin 1104) = 203945748940358395473515415382 := by decide +kernel
  have he : certE (⟨902, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hp : parent2 (⟨902, by omega⟩ : Fin 1104) 2 = 2 := by decide +kernel
  have hs : (l2At (⟨902, by omega⟩ : Fin 1104)).2.2 = 21076548236 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_903 :
    ((certNum ⟨903, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨903, by omega⟩) ⟨903, by omega⟩ (certE ⟨903, by omega⟩) := by
  have hm : certMode (⟨903, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨903, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨903, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨903, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨903, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_904 :
    ((certNum ⟨904, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨904, by omega⟩) ⟨904, by omega⟩ (certE ⟨904, by omega⟩) := by
  have hm : certMode (⟨904, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨904, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨904, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨904, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨904, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_905 :
    ((certNum ⟨905, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨905, by omega⟩) ⟨905, by omega⟩ (certE ⟨905, by omega⟩) := by
  have hm : certMode (⟨905, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨905, by omega⟩ : Fin 1104) = 180564518316096529049577803162 := by decide +kernel
  have he : certE (⟨905, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then -6 else if j.val = 2 then -6 else 7)) := by decide +kernel
  have hp : parent2 (⟨905, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨905, by omega⟩ : Fin 1104)).2.2 = 18074729281 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_906 :
    ((certNum ⟨906, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨906, by omega⟩) ⟨906, by omega⟩ (certE ⟨906, by omega⟩) := by
  have hm : certMode (⟨906, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨906, by omega⟩ : Fin 1104) = 203771305144373430845298782202 := by decide +kernel
  have he : certE (⟨906, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨906, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨906, by omega⟩ : Fin 1104)).2.2 = 21053697512 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_907 :
    ((certNum ⟨907, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨907, by omega⟩) ⟨907, by omega⟩ (certE ⟨907, by omega⟩) := by
  have hm : certMode (⟨907, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨907, by omega⟩ : Fin 1104) = 151642474006483812331197673 := by decide +kernel
  have he : certE (⟨907, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -2 else if j.val = 1 then -3 else if j.val = 2 then -7 else 2)) := by decide +kernel
  have hp : parent2 (⟨907, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨907, by omega⟩ : Fin 1104)).2.2 = 5807209 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_908 :
    ((certNum ⟨908, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨908, by omega⟩) ⟨908, by omega⟩ (certE ⟨908, by omega⟩) := by
  have hm : certMode (⟨908, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨908, by omega⟩ : Fin 1104) = 203772788047928653263152599755 := by decide +kernel
  have he : certE (⟨908, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨908, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨908, by omega⟩ : Fin 1104)).2.2 = 21053891734 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_909 :
    ((certNum ⟨909, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨909, by omega⟩) ⟨909, by omega⟩ (certE ⟨909, by omega⟩) := by
  have hm : certMode (⟨909, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨909, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨909, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨909, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨909, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_910 :
    ((certNum ⟨910, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨910, by omega⟩) ⟨910, by omega⟩ (certE ⟨910, by omega⟩) := by
  have hm : certMode (⟨910, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨910, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨910, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨910, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨910, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_911 :
    ((certNum ⟨911, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨911, by omega⟩) ⟨911, by omega⟩ (certE ⟨911, by omega⟩) := by
  have hm : certMode (⟨911, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨911, by omega⟩ : Fin 1104) = 180557547952951506738607836243 := by decide +kernel
  have he : certE (⟨911, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then 5 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hp : parent2 (⟨911, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨911, by omega⟩ : Fin 1104)).2.2 = 18073852824 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_912 :
    ((certNum ⟨912, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨912, by omega⟩) ⟨912, by omega⟩ (certE ⟨912, by omega⟩) := by
  have hm : certMode (⟨912, by omega⟩ : Fin 1104) = 1 := by decide +kernel
  have hn : certNum (⟨912, by omega⟩ : Fin 1104) = 203773186842970085611455763960 := by decide +kernel
  have he : certE (⟨912, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hp : parent2 (⟨912, by omega⟩ : Fin 1104) 1 = 2 := by decide +kernel
  have hs : (l2At (⟨912, by omega⟩ : Fin 1104)).2.2 = 21053943966 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_913 :
    ((certNum ⟨913, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨913, by omega⟩) ⟨913, by omega⟩ (certE ⟨913, by omega⟩) := by
  have hm : certMode (⟨913, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨913, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have he : certE (⟨913, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hp : parent2 (⟨913, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨913, by omega⟩ : Fin 1104)).2.2 = 0 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_914 :
    ((certNum ⟨914, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨914, by omega⟩) ⟨914, by omega⟩ (certE ⟨914, by omega⟩) := by
  have hm : certMode (⟨914, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨914, by omega⟩ : Fin 1104) = 179834902006281709493343804707 := by decide +kernel
  have he : certE (⟨914, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then -7 else if j.val = 2 then -5 else 7) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then 1 else -8)) := by decide +kernel
  have hp : parent2 (⟨914, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨914, by omega⟩ : Fin 1104)).2.2 = 17983047243 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_915 :
    ((certNum ⟨915, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨915, by omega⟩) ⟨915, by omega⟩ (certE ⟨915, by omega⟩) := by
  have hm : certMode (⟨915, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨915, by omega⟩ : Fin 1104) = 179834856398279713810986769829 := by decide +kernel
  have he : certE (⟨915, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then -7 else if j.val = 2 then -5 else 7) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then 1 else -8)) := by decide +kernel
  have hp : parent2 (⟨915, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨915, by omega⟩ : Fin 1104)).2.2 = 17983041516 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_916 :
    ((certNum ⟨916, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨916, by omega⟩) ⟨916, by omega⟩ (certE ⟨916, by omega⟩) := by
  have hm : certMode (⟨916, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨916, by omega⟩ : Fin 1104) = 179834957146799947684425077194 := by decide +kernel
  have he : certE (⟨916, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then -7 else if j.val = 2 then -5 else 7) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then 1 else -8)) := by decide +kernel
  have hp : parent2 (⟨916, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨916, by omega⟩ : Fin 1104)).2.2 = 17983054167 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_917 :
    ((certNum ⟨917, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨917, by omega⟩) ⟨917, by omega⟩ (certE ⟨917, by omega⟩) := by
  have hm : certMode (⟨917, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨917, by omega⟩ : Fin 1104) = 179835663014536730678878276574 := by decide +kernel
  have he : certE (⟨917, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then -7 else if j.val = 2 then -5 else 7) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then 1 else -8)) := by decide +kernel
  have hp : parent2 (⟨917, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨917, by omega⟩ : Fin 1104)).2.2 = 17983142803 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_918 :
    ((certNum ⟨918, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨918, by omega⟩) ⟨918, by omega⟩ (certE ⟨918, by omega⟩) := by
  have hm : certMode (⟨918, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨918, by omega⟩ : Fin 1104) = 179835099648833260037028020195 := by decide +kernel
  have he : certE (⟨918, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then -7 else if j.val = 2 then -5 else 7) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then 1 else -8)) := by decide +kernel
  have hp : parent2 (⟨918, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨918, by omega⟩ : Fin 1104)).2.2 = 17983072061 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

theorem cert_919 :
    ((certNum ⟨919, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨919, by omega⟩) ⟨919, by omega⟩ (certE ⟨919, by omega⟩) := by
  have hm : certMode (⟨919, by omega⟩ : Fin 1104) = 0 := by decide +kernel
  have hn : certNum (⟨919, by omega⟩ : Fin 1104) = 179835661883697228203632442614 := by decide +kernel
  have he : certE (⟨919, by omega⟩ : Fin 1104) = fun (a : Fin 3) (j : Fin 4) =>
      (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then -7 else if j.val = 2 then -5 else 7) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then 1 else -8)) := by decide +kernel
  have hp : parent2 (⟨919, by omega⟩ : Fin 1104) 0 = 2 := by decide +kernel
  have hs : (l2At (⟨919, by omega⟩ : Fin 1104)).2.2 = 17983142661 := by decide +kernel
  rw [hm, hn, he]
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_param0 _ _ hp, PG_param1 _ _ hp, PG_param2 _ _ hp, hs]
  rw [logLo0, logLo1, logLo2, logLo3, logHi0, logHi1, logHi2, logHi3]
  norm_num [qvalQ, D]

end MME.L2Cert

theorem solution : ∀ j : Fin 92,
    ((certNum ⟨828 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨828 + j.val, by omega⟩) ⟨828 + j.val, by omega⟩
        (certE ⟨828 + j.val, by omega⟩) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.cert_828
  | ⟨1, _⟩ => exact MME.L2Cert.cert_829
  | ⟨2, _⟩ => exact MME.L2Cert.cert_830
  | ⟨3, _⟩ => exact MME.L2Cert.cert_831
  | ⟨4, _⟩ => exact MME.L2Cert.cert_832
  | ⟨5, _⟩ => exact MME.L2Cert.cert_833
  | ⟨6, _⟩ => exact MME.L2Cert.cert_834
  | ⟨7, _⟩ => exact MME.L2Cert.cert_835
  | ⟨8, _⟩ => exact MME.L2Cert.cert_836
  | ⟨9, _⟩ => exact MME.L2Cert.cert_837
  | ⟨10, _⟩ => exact MME.L2Cert.cert_838
  | ⟨11, _⟩ => exact MME.L2Cert.cert_839
  | ⟨12, _⟩ => exact MME.L2Cert.cert_840
  | ⟨13, _⟩ => exact MME.L2Cert.cert_841
  | ⟨14, _⟩ => exact MME.L2Cert.cert_842
  | ⟨15, _⟩ => exact MME.L2Cert.cert_843
  | ⟨16, _⟩ => exact MME.L2Cert.cert_844
  | ⟨17, _⟩ => exact MME.L2Cert.cert_845
  | ⟨18, _⟩ => exact MME.L2Cert.cert_846
  | ⟨19, _⟩ => exact MME.L2Cert.cert_847
  | ⟨20, _⟩ => exact MME.L2Cert.cert_848
  | ⟨21, _⟩ => exact MME.L2Cert.cert_849
  | ⟨22, _⟩ => exact MME.L2Cert.cert_850
  | ⟨23, _⟩ => exact MME.L2Cert.cert_851
  | ⟨24, _⟩ => exact MME.L2Cert.cert_852
  | ⟨25, _⟩ => exact MME.L2Cert.cert_853
  | ⟨26, _⟩ => exact MME.L2Cert.cert_854
  | ⟨27, _⟩ => exact MME.L2Cert.cert_855
  | ⟨28, _⟩ => exact MME.L2Cert.cert_856
  | ⟨29, _⟩ => exact MME.L2Cert.cert_857
  | ⟨30, _⟩ => exact MME.L2Cert.cert_858
  | ⟨31, _⟩ => exact MME.L2Cert.cert_859
  | ⟨32, _⟩ => exact MME.L2Cert.cert_860
  | ⟨33, _⟩ => exact MME.L2Cert.cert_861
  | ⟨34, _⟩ => exact MME.L2Cert.cert_862
  | ⟨35, _⟩ => exact MME.L2Cert.cert_863
  | ⟨36, _⟩ => exact MME.L2Cert.cert_864
  | ⟨37, _⟩ => exact MME.L2Cert.cert_865
  | ⟨38, _⟩ => exact MME.L2Cert.cert_866
  | ⟨39, _⟩ => exact MME.L2Cert.cert_867
  | ⟨40, _⟩ => exact MME.L2Cert.cert_868
  | ⟨41, _⟩ => exact MME.L2Cert.cert_869
  | ⟨42, _⟩ => exact MME.L2Cert.cert_870
  | ⟨43, _⟩ => exact MME.L2Cert.cert_871
  | ⟨44, _⟩ => exact MME.L2Cert.cert_872
  | ⟨45, _⟩ => exact MME.L2Cert.cert_873
  | ⟨46, _⟩ => exact MME.L2Cert.cert_874
  | ⟨47, _⟩ => exact MME.L2Cert.cert_875
  | ⟨48, _⟩ => exact MME.L2Cert.cert_876
  | ⟨49, _⟩ => exact MME.L2Cert.cert_877
  | ⟨50, _⟩ => exact MME.L2Cert.cert_878
  | ⟨51, _⟩ => exact MME.L2Cert.cert_879
  | ⟨52, _⟩ => exact MME.L2Cert.cert_880
  | ⟨53, _⟩ => exact MME.L2Cert.cert_881
  | ⟨54, _⟩ => exact MME.L2Cert.cert_882
  | ⟨55, _⟩ => exact MME.L2Cert.cert_883
  | ⟨56, _⟩ => exact MME.L2Cert.cert_884
  | ⟨57, _⟩ => exact MME.L2Cert.cert_885
  | ⟨58, _⟩ => exact MME.L2Cert.cert_886
  | ⟨59, _⟩ => exact MME.L2Cert.cert_887
  | ⟨60, _⟩ => exact MME.L2Cert.cert_888
  | ⟨61, _⟩ => exact MME.L2Cert.cert_889
  | ⟨62, _⟩ => exact MME.L2Cert.cert_890
  | ⟨63, _⟩ => exact MME.L2Cert.cert_891
  | ⟨64, _⟩ => exact MME.L2Cert.cert_892
  | ⟨65, _⟩ => exact MME.L2Cert.cert_893
  | ⟨66, _⟩ => exact MME.L2Cert.cert_894
  | ⟨67, _⟩ => exact MME.L2Cert.cert_895
  | ⟨68, _⟩ => exact MME.L2Cert.cert_896
  | ⟨69, _⟩ => exact MME.L2Cert.cert_897
  | ⟨70, _⟩ => exact MME.L2Cert.cert_898
  | ⟨71, _⟩ => exact MME.L2Cert.cert_899
  | ⟨72, _⟩ => exact MME.L2Cert.cert_900
  | ⟨73, _⟩ => exact MME.L2Cert.cert_901
  | ⟨74, _⟩ => exact MME.L2Cert.cert_902
  | ⟨75, _⟩ => exact MME.L2Cert.cert_903
  | ⟨76, _⟩ => exact MME.L2Cert.cert_904
  | ⟨77, _⟩ => exact MME.L2Cert.cert_905
  | ⟨78, _⟩ => exact MME.L2Cert.cert_906
  | ⟨79, _⟩ => exact MME.L2Cert.cert_907
  | ⟨80, _⟩ => exact MME.L2Cert.cert_908
  | ⟨81, _⟩ => exact MME.L2Cert.cert_909
  | ⟨82, _⟩ => exact MME.L2Cert.cert_910
  | ⟨83, _⟩ => exact MME.L2Cert.cert_911
  | ⟨84, _⟩ => exact MME.L2Cert.cert_912
  | ⟨85, _⟩ => exact MME.L2Cert.cert_913
  | ⟨86, _⟩ => exact MME.L2Cert.cert_914
  | ⟨87, _⟩ => exact MME.L2Cert.cert_915
  | ⟨88, _⟩ => exact MME.L2Cert.cert_916
  | ⟨89, _⟩ => exact MME.L2Cert.cert_917
  | ⟨90, _⟩ => exact MME.L2Cert.cert_918
  | ⟨91, _⟩ => exact MME.L2Cert.cert_919
  | ⟨n + 92, h⟩ => exact absurd h (by omega)
