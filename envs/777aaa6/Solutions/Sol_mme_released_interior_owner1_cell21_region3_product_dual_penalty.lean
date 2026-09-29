-- Prove2me | solution 1 for mme_released_interior_owner1_cell21_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:54.20327+00:00
-- url     : https://prove2.me/submissions/36b33df5-9af6-45c6-89d5-da114cdd21df

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(26147658655750000000000000000000000 / 1248467824281239476105854901757562033), (48539107385000000000000000000000000 / 1248467824281239476105854901757562033), (26147754314312500000000000000000000 / 1248467824281239476105854901757562033), (1 / 1), (1 / 1)], ![(38968946189 / 1000000000000), (2292216552459 / 1000000000000), (17111120177471 / 1000000000000), (2292225045713 / 1000000000000), (38968949353 / 1000000000000)], ![(100702939163 / 250000000000), (167831466697 / 200000000000), (402813225601 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1932956343269 / 500000000000), (-129892101081 / 40000000000), (-1932954514073 / 500000000000), (0 / 1), (0 / 1)], ![(-1622495100797 / 500000000000), (165903855253 / 200000000000), (2839728554929 / 1000000000000), (207380745379 / 250000000000), (-3244990120401 / 1000000000000)], ![(-181857186249 / 200000000000), (-43839266271 / 250000000000), (-454641142257 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3865912686537 / 1000000000000), (-202956407939 / 62500000000), (-773181805629 / 200000000000), (0 / 1), (0 / 1)], ![(-3244990201593 / 1000000000000), (414759638133 / 500000000000), (283972855493 / 100000000000), (829522981517 / 1000000000000), (-8112475301 / 2500000000)], ![(-227321482811 / 250000000000), (-175357065083 / 1000000000000), (-909282284513 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-250630898047 / 31250000000), (-321174670787 / 100000000000), (-1935466433489 / 1000000000000), (-3327065546597 / 1000000000000), (-29146551859 / 50000000000), (-3327065465423 / 1000000000000), (-1935466387097 / 1000000000000), (-1605873439597 / 500000000000), (-8020181513371 / 1000000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020188737503 / 1000000000000), (-3211746707869 / 1000000000000), (-120966652093 / 62500000000), (-831766386649 / 250000000000), (-582931037179 / 1000000000000), (-1663532732711 / 500000000000), (-241933298387 / 125000000000), (-3211746879193 / 1000000000000), (-802018151337 / 100000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 1 21 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
