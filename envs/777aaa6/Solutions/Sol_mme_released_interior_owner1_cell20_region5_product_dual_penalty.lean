-- Prove2me | solution 1 for mme_released_interior_owner1_cell20_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:50.491075+00:00
-- url     : https://prove2.me/submissions/24eaf93d-2963-41ba-8917-fb006551da8b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 1 20 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(18472786602625000000000000000000000 / 677422886990660993111378132128877093), (106081687869875000000000000000000000 / 2032268660971982979334134396386631279), (55406367698000000000000000000000000 / 2032268660971982979334134396386631279), (1 / 1), (1 / 1)], ![(32956737451 / 200000000000), (2485499564827 / 1000000000000), (2485231608523 / 1000000000000), (41182024773 / 250000000000), (1 / 1)], ![(33939882197 / 200000000000), (1205666506521 / 500000000000), (9418246507 / 3906250000), (169646431051 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3601997071679 / 1000000000000), (-2952698577401 / 1000000000000), (-3602213487459 / 1000000000000), (0 / 1), (0 / 1)], ![(-180312165151 / 100000000000), (910473671467 / 1000000000000), (91036585783 / 100000000000), (-450864762157 / 250000000000), (0 / 1)], ![(-443431644417 / 250000000000), (440089856017 / 500000000000), (220017772751 / 250000000000), (-1774038825103 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1800998535839 / 500000000000), (-14763492887 / 5000000000), (-1801106743729 / 500000000000), (0 / 1), (0 / 1)], ![(-1803121651509 / 1000000000000), (227618417867 / 250000000000), (910365857831 / 1000000000000), (-1803459048627 / 1000000000000), (0 / 1)], ![(-1773726577667 / 1000000000000), (176035942407 / 200000000000), (176014218201 / 200000000000), (-887019412551 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-1132314247649 / 250000000000), (-1811033558547 / 1000000000000), (-2234655862931 / 500000000000), (-3250410405789 / 500000000000), (-1162290581723 / 1000000000000), (-581145692951 / 500000000000), (-3250397844751 / 500000000000), (-2234661831 / 500000000), (-1811033539671 / 1000000000000), (-4529244677313 / 1000000000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-905851398119 / 200000000000), (-905516779273 / 500000000000), (-4469311725861 / 1000000000000), (-6500820811577 / 1000000000000), (-581145290861 / 500000000000), (-1162291385901 / 1000000000000), (-6500795689501 / 1000000000000), (-4469323661999 / 1000000000000), (-181103353967 / 100000000000), (-70769448083 / 15625000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 1 20 5 c : ℝ) / 1000000000000) ≤
          (1641 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1641 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1641 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
