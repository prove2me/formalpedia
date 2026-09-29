-- Prove2me | solution 1 for mme_released_interior_owner5_cell32_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:23:14.122784+00:00
-- url     : https://prove2.me/submissions/f64bfad6-ead0-4b81-8fcc-2dad31b7f9d6

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 5 32 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(19512668411 / 500000000000), (583202060103 / 250000000000), (16630398238771 / 1000000000000), (2332802590279 / 1000000000000), (1951266749 / 50000000000)], ![(420232974987 / 1000000000000), (389733543943 / 500000000000), (210116013221 / 500000000000), (1 / 1), (1 / 1)], ![(403995379896000000000000000000000000 / 19732849107117153070467680671456005007), (844550924535000000000000000000000000 / 19732849107117153070467680671456005007), (403994696062000000000000000000000000 / 19732849107117153070467680671456005007), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3243544181689 / 1000000000000), (423536397619 / 500000000000), (2811232239927 / 1000000000000), (211767593301 / 250000000000), (-324354422889 / 100000000000)], ![(-433473009573 / 500000000000), (-12457240673 / 50000000000), (-866948276337 / 1000000000000), (0 / 1), (0 / 1)], ![(-1944318275709 / 500000000000), (-157561747879 / 50000000000), (-3888638244097 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-405443022711 / 125000000000), (847072795239 / 1000000000000), (351404029991 / 125000000000), (169414074641 / 200000000000), (-3243544228889 / 1000000000000)], ![(-173389203829 / 200000000000), (-249144813459 / 1000000000000), (-54184267271 / 62500000000), (0 / 1), (0 / 1)], ![(-3888636551417 / 1000000000000), (-3151234957579 / 1000000000000), (-15189993141 / 3906250000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 5 32).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7999126799399 / 1000000000000), (-3290711056367 / 1000000000000), (-972176285501 / 500000000000), (-79277763653 / 25000000000), (-58914753111 / 100000000000), (-792777624017 / 250000000000), (-121522002509 / 62500000000), (-822677549411 / 250000000000), (-7999130701053 / 1000000000000)] : List ℚ).getD
    ((seed 5 32).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-3999563399699 / 500000000000), (-1645355528183 / 500000000000), (-1944352571001 / 1000000000000), (-3171110546119 / 1000000000000), (-589147531109 / 1000000000000), (-3171110496067 / 1000000000000), (-1944352040143 / 1000000000000), (-3290710197643 / 1000000000000), (-1999782675263 / 250000000000)] : List ℚ).getD
    ((seed 5 32).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 5 32 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
