-- Prove2me | solution 1 for mme_released_interior_owner1_cell12_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:31.883872+00:00
-- url     : https://prove2.me/submissions/e553892e-26b6-4585-a091-f454554cf867

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 1 12 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1915777684750000000000000000000000 / 87247018636812978513026477574372263), (32568871212000000000000000000000000 / 1483199316825820634721450118764328471), (1 / 1), (1 / 1), (1 / 1)], ![(276646309467 / 1000000000000), (56513562537 / 40000000000), (706433596079 / 500000000000), (138332279809 / 500000000000), (1 / 1)], ![(53255521563 / 1000000000000), (1983733024791 / 1000000000000), (1716746924509 / 125000000000), (198381392413 / 100000000000), (13313893119 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-763723949651 / 200000000000), (-477324971601 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1285015449807 / 1000000000000), (172800600067 / 500000000000), (43202638663 / 125000000000), (-160618685341 / 125000000000), (0 / 1)], ![(-586530757689 / 200000000000), (68498043569 / 100000000000), (523974543747 / 200000000000), (685021216223 / 1000000000000), (-183290802027 / 62500000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1909309874127 / 500000000000), (-3818599772807 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-642507724903 / 500000000000), (69120240027 / 200000000000), (69124221861 / 200000000000), (-1284949482727 / 1000000000000), (0 / 1)], ![(-733163447111 / 250000000000), (684980435691 / 1000000000000), (163742044921 / 62500000000), (21406913007 / 31250000000), (-2932652832431 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([7, 2, 5, 12, 12, 5, 2, 7] : List ℤ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-1104647198817 / 250000000000), (-170625184043 / 200000000000), (-2787997331891 / 1000000000000), (-1004536003953 / 125000000000), (-8036203044953 / 1000000000000), (-557599645563 / 200000000000), (-853125853937 / 1000000000000), (-4418594006369 / 1000000000000)] : List ℚ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4418588795267 / 1000000000000), (-426562960107 / 500000000000), (-278799733189 / 100000000000), (-8036288031623 / 1000000000000), (-1004525380619 / 125000000000), (-1393999113907 / 500000000000), (-53320365871 / 62500000000), (-138081062699 / 31250000000)] : List ℚ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 12) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 12 =>
        (splitWeight 1 12 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 12, ∏ i, weights i (c.val i) ≤ 1 := by
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
