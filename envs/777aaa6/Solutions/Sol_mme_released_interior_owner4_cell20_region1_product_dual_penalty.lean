-- Prove2me | solution 1 for mme_released_interior_owner4_cell20_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:16:59.03146+00:00
-- url     : https://prove2.me/submissions/c166d687-3a75-4865-af9d-12e0a6f3a1d3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 4 20 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(444397260799 / 1000000000000), (863737505169 / 1000000000000), (444439605819 / 1000000000000), (1 / 1), (1 / 1)], ![(84460469469000000000000000000000000 / 7959337181119115709405877757637205799), (1224929691202000000000000000000000000 / 7959337181119115709405877757637205799), (1224988257292500000000000000000000000 / 7959337181119115709405877757637205799), (84472029960000000000000000000000000 / 7959337181119115709405877757637205799), (1 / 1)], ![(175008338987 / 1000000000000), (295090281693 / 125000000000), (18886673243 / 8000000000), (175034565413 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-162207277011 / 200000000000), (-146486369801 / 1000000000000), (-810941103183 / 1000000000000), (0 / 1), (0 / 1)], ![(-4545817398701 / 1000000000000), (-935731140137 / 500000000000), (-1871414469619 / 1000000000000), (-454568053349 / 100000000000), (0 / 1)], ![(-43573041371 / 25000000000), (429483805927 / 500000000000), (429507506127 / 500000000000), (-1742771807917 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-405518192527 / 500000000000), (-732431849 / 5000000000), (-405470551591 / 500000000000), (0 / 1), (0 / 1)], ![(-45458173987 / 10000000000), (-1871462280273 / 1000000000000), (-935707234809 / 500000000000), (-4545680533489 / 1000000000000), (0 / 1)], ![(-1742921654839 / 1000000000000), (171793522371 / 200000000000), (171803002451 / 200000000000), (-435692951979 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2249863232871 / 500000000000), (-6421420595919 / 1000000000000), (-455790652841 / 250000000000), (-115900392391 / 100000000000), (-4427114693253 / 1000000000000), (-885424286811 / 200000000000), (-1159003514623 / 1000000000000), (-1823162682163 / 1000000000000), (-1605358398313 / 250000000000), (-4499732266317 / 1000000000000)] : List ℚ).getD
    ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4499726465741 / 1000000000000), (-3210710297959 / 500000000000), (-1823162611363 / 1000000000000), (-1159003923909 / 1000000000000), (-1106778673313 / 250000000000), (-2213560717027 / 500000000000), (-579501757311 / 500000000000), (-911581341081 / 500000000000), (-6421433593251 / 1000000000000), (-1124933066579 / 250000000000)] : List ℚ).getD
    ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 20 1 c : ℝ) / 1000000000000) ≤
          (400 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (400 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((400 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
