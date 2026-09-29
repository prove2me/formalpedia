-- Prove2me | solution 1 for mme_released_interior_owner2_cell13_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:17:03.765988+00:00
-- url     : https://prove2.me/submissions/4c9e5cc8-d6dc-421b-b20b-195f77946fb0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 2 13 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(393046057681 / 1000000000000), (196525432987 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(3332428716875000000000000000000000 / 1099939149056557924918976308241267939), (18151307619312500000000000000000000 / 157134164150936846416996615463038277), (821938039196125000000000000000000000 / 1099939149056557924918976308241267939), (127061997659312500000000000000000000 / 1099939149056557924918976308241267939), (3332428754562500000000000000000000 / 1099939149056557924918976308241267939)], ![(17097482621 / 62500000000), (718421458299 / 500000000000), (1436861086413 / 1000000000000), (136782152557 / 500000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-933828478863 / 1000000000000), (-933816245529 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-289965437783 / 50000000000), (-431671477181 / 200000000000), (-291345124109 / 1000000000000), (-2158335000329 / 1000000000000), (-5799308744351 / 1000000000000)], ![(-648117659609 / 500000000000), (362448287689 / 1000000000000), (362460933261 / 1000000000000), (-129621856551 / 100000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-466914239431 / 500000000000), (-116727030691 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-5799308755659 / 1000000000000), (-134897336619 / 62500000000), (-72836281027 / 250000000000), (-269791875041 / 125000000000), (-115986174887 / 20000000000)], ![(-1296235319217 / 1000000000000), (36244828769 / 100000000000), (181230466631 / 500000000000), (-1296218565509 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-8029343565967 / 1000000000000), (-1097101107571 / 250000000000), (-42651760909 / 15625000000), (-215678167427 / 250000000000), (-862713081949 / 1000000000000), (-272971519151 / 100000000000), (-877677313021 / 200000000000), (-802937254153 / 100000000000)] : List ℚ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-4014671782983 / 500000000000), (-4388404430283 / 1000000000000), (-109188507927 / 40000000000), (-862712669707 / 1000000000000), (-215678270487 / 250000000000), (-2729715191509 / 1000000000000), (-274274160319 / 62500000000), (-8029372541529 / 1000000000000)] : List ℚ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 2 13 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
