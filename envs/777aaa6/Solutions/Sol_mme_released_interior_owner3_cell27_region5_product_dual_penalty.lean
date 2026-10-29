-- Prove2me | solution 1 for mme_released_interior_owner3_cell27_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:31:55.350826+00:00
-- url     : https://prove2.me/submissions/ac147c21-5e0d-4620-a73b-a7e113c85d8d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 3 27 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(5325341043817 / 100000000000000), (744657957902179 / 1000000000000000), (372328881381423 / 500000000000000), (53253967232429 / 1000000000000000), (1 / 1)], ![(22523123701479 / 500000000000000), (135848805222041 / 200000000000000), (339622179077873 / 500000000000000), (45045691093217 / 1000000000000000), (1 / 1)], ![(322871308633927 / 1000000000000000), (618218776691199 / 1000000000000000), (161435698609333 / 500000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 0, 0, 4, 0], ![4, 1, 1, 4, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1466346715328109 / 500000000000000), (-294830282938843 / 1000000000000000), (-294830544991181 / 1000000000000000), (-366585371893787 / 125000000000000), (0 / 1)], ![(-3100065596888803 / 1000000000000000), (-38677482554659 / 100000000000000), (-19338716835049 / 50000000000000), (-775019486677917 / 250000000000000), (0 / 1)], ![(-1130501460433883 / 1000000000000000), (-480912876579413 / 1000000000000000), (-35328162064639 / 31250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1466346715328107 / 500000000000000), (-147415141469421 / 500000000000000), (-14741527249559 / 50000000000000), (-733170743787573 / 250000000000000), (0 / 1)], ![(-1550032798444399 / 500000000000000), (-96693706386647 / 250000000000000), (-386774336700979 / 1000000000000000), (-193754871669479 / 62500000000000), (0 / 1)], ![(-28262536510847 / 25000000000000), (-480912876579411 / 1000000000000000), (-565250593034223 / 500000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 3, 6, 9, 2, 2, 9, 6, 3, 7] : List ℤ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-4529357977841283 / 1000000000000000), (-113223989081049 / 62500000000000), (-4453620163454651 / 1000000000000000), (-1621328337678331 / 250000000000000), (-36332937112721 / 31250000000000), (-36332960489013 / 31250000000000), (-1297058115380889 / 200000000000000), (-2226814905894529 / 500000000000000), (-56611993054671 / 31250000000000), (-4529345652561891 / 1000000000000000)] : List ℚ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-1132339494460319 / 250000000000000), (-1811583825296781 / 1000000000000000), (-890724032690929 / 200000000000000), (-1297062670142663 / 200000000000000), (-1162653987607069 / 1000000000000000), (-1162654735648413 / 1000000000000000), (-1621322644226109 / 250000000000000), (-1113407452947263 / 250000000000000), (-1811583777749469 / 1000000000000000), (-1132336413140471 / 250000000000000)] : List ℚ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 3 27 5 c : ℝ) / 1000000000000) ≤
          (1592 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1592 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1592 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
