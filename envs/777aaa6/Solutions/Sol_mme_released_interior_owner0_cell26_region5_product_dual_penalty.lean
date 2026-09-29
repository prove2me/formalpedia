-- Prove2me | solution 1 for mme_released_interior_owner0_cell26_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:43:55.685205+00:00
-- url     : https://prove2.me/submissions/14872a25-3e01-4ad9-a213-09e5bc8253e0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(22047348866125000000000000000000000 / 1984747494210554850036977185871014623), (97644187561250000000000000000000000 / 661582498070184950012325728623671541), (97651873251000000000000000000000000 / 661582498070184950012325728623671541), (22052528867750000000000000000000000 / 1984747494210554850036977185871014623), (1 / 1)], ![(44494062707 / 100000000000), (216189905373 / 250000000000), (445010638821 / 1000000000000), (1 / 1), (1 / 1)], ![(16843860367 / 100000000000), (2457908226279 / 1000000000000), (1229050774993 / 500000000000), (168478442631 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-562506827031 / 125000000000), (-1913304557047 / 1000000000000), (-1913225848959 / 1000000000000), (-4499819694887 / 1000000000000), (0 / 1)], ![(-809814428033 / 1000000000000), (-145303704899 / 1000000000000), (-809657089639 / 1000000000000), (0 / 1), (0 / 1)], ![(-3562367931 / 2000000000), (899310673701 / 1000000000000), (899389324361 / 1000000000000), (-1780947474283 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4500054616247 / 1000000000000), (-956652278523 / 500000000000), (-956612924479 / 500000000000), (-2249909847443 / 500000000000), (0 / 1)], ![(-6326675219 / 7812500000), (-72651852449 / 500000000000), (-404828544819 / 500000000000), (0 / 1), (0 / 1)], ![(-1781183965499 / 1000000000000), (449655336851 / 500000000000), (449694662181 / 500000000000), (-890473737141 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-6412256051699 / 1000000000000), (-4412208643057 / 1000000000000), (-225306914609 / 50000000000), (-36227872779 / 31250000000), (-182336732261 / 100000000000), (-1823367302261 / 1000000000000), (-1159291871591 / 1000000000000), (-1126534683791 / 250000000000), (-176488388409 / 40000000000), (-10259612189 / 1600000000)] : List ℚ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-3206128025849 / 500000000000), (-275763040191 / 62500000000), (-4506138292179 / 1000000000000), (-1159291928927 / 1000000000000), (-1823367322609 / 1000000000000), (-91168365113 / 50000000000), (-115929187159 / 100000000000), (-4506138735163 / 1000000000000), (-275763106889 / 62500000000), (-1603064404531 / 250000000000)] : List ℚ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 0 26 5 c : ℝ) / 1000000000000) ≤
          (428 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (428 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((428 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
