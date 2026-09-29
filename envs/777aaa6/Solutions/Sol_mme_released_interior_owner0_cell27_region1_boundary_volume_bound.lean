-- Prove2me | solution 1 for mme_released_interior_owner0_cell27_region1_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T07:38:38.001248+00:00
-- url     : https://prove2.me/submissions/8b732666-0e7b-434e-a8d8-cd3d5ede83f4

import Theorems.Thm_mme_rational_boundary_volume_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed
open MME.CompleteSplit MME.RecursiveYZ MME.RecursiveYZ.Boundary

private abbrev Split := ReleasedInterior.Split 27
private def rowIndex (c : Split) (z : Fin 3) : ℕ :=
  3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def massNumerator (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 318724180558569058208078445566670, 0, 5283060692857136107693843108866660, 0, 318724180558569058208078445566670, 0, 0]),
    (48, [0, 0, 0, 0, 0, 435800938336625080755000000000000, 0, 435800938336625080755000000000000, 0]),
    (122, [0, 3173754671381763022590000000000000, 0, 3173754671381763022590000000000000, 0, 0, 0, 0, 0]),
    (157, [0, 0, 323211521707247962940871853545660, 0, 5701086299349030119298256292908680, 0, 323211521707247962940871853545660, 0, 0]),
    (182, [0, 0, 4870097049277105280856138255832800, 0, 75587671880714399362847723488334400, 0, 4870097049277105280856138255832800, 0, 0]),
    (229, [0, 435800938336625080755000000000000, 0, 435800938336625080755000000000000, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 2960254526987137112055000000000000, 0, 2960254526987137112055000000000000, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def logScale (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (48, [0, 0, 0, 0, 0, 1, 0, 1, 0]),
    (122, [0, 1, 0, 1, 0, 0, 0, 0, 0]),
    (157, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (182, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (229, [0, 1, 0, 1, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 1, 0, 1, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def lowerMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 2921851622006, 0, 113916827599, 0, 2921851622006, 0, 0]),
    (48, [0, 0, 0, 0, 0, 693147180560, 0, 693147180560, 0]),
    (122, [0, 693147180560, 0, 693147180560, 0, 0, 0, 0, 0]),
    (157, [0, 0, 2977510810601, 0, 107405770961, 0, 2977510810601, 0, 0]),
    (182, [0, 0, 2863387218325, 0, 121207883677, 0, 2863387218325, 0, 0]),
    (229, [0, 693147180560, 0, 693147180560, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 693147180560, 0, 693147180560, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def upperMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 2921851622005, 0, 113916827598, 0, 2921851622005, 0, 0]),
    (48, [0, 0, 0, 0, 0, 693147180559, 0, 693147180559, 0]),
    (122, [0, 693147180559, 0, 693147180559, 0, 0, 0, 0, 0]),
    (157, [0, 0, 2977510810600, 0, 107405770960, 0, 2977510810600, 0, 0]),
    (182, [0, 0, 2863387218324, 0, 121207883676, 0, 2863387218324, 0, 0]),
    (229, [0, 693147180559, 0, 693147180559, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 693147180559, 0, 693147180559, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def boundNumerator (c : Split) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19469875387, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2006937488, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14615680390, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20888150033, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 280359098701, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2006937488, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13632475890, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (rowIndex c z) 0

private def x (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℚ :=
  (massNumerator c z w : ℚ) / 1000000000000000000000000000000000000
private def lower (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℚ :=
  -(lowerMagnitude c z w : ℚ) / 1000000000000
private def upper (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℚ :=
  -(upperMagnitude c z w : ℚ) / 1000000000000
private def bound (c : Split) (z : Fin 3) : ℚ :=
  (boundNumerator c z : ℚ) / 1000000000000

private theorem log_bounds (c : Split) (z : Fin 3) (w : CompleteWord 2)
    (hp : 0 < x c z w / ∑ v, x c z v) :
    (lower c z w : ℝ) ≤ Real.log ((x c z w / ∑ v, x c z v : ℚ) : ℝ) ∧
      Real.log ((x c z w / ∑ v, x c z v : ℚ) : ℝ) ≤ (upper c z w : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale c z w) 16
  all_goals revert c z w; decide +kernel

/-- The actual free-mode histogram of a released boundary child has a
certified entropy and letter-volume lower bound at its physical scale. -/
theorem solution
    (c : ReleasedInterior.Split 27) (z : Fin 3) (hz : (c.val z).val = 0) :
    (denominator : ℝ) ^ 4 *
      ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19469875387, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2006937488, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14615680390, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20888150033, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 280359098701, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2006937488, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13632475890, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
        (3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val) 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 27 (z + 1) ⟨1, c⟩ w : ℝ)) +
        (∑ w, (ReleasedInterior.integerProfile 0 27 (z + 1) ⟨1, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ c z w, 0 ≤ x c z w := by decide +kernel
  have hcert : ∀ c z, bound c z ≤
      (∑ w, x c z w) * (-(∑ w, (x c z w / ∑ v, x c z v) * upper c z w)) +
        (∑ w, x c z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x c z) (hx c z) ones
    (lower c z) (upper c z) (log_bounds c z) (bound c z) (hcert c z)
    ((denominator : ℝ) ^ 4) (by positivity)
  have hid : ∀ (c : Split) (z : Fin 3), (c.val z).val = 0 → ∀ w,
      (denominator : ℚ) ^ 4 * x c z w = (ReleasedInterior.integerProfile 0 27 (z + 1) ⟨1, c⟩ w : ℚ) := by
    decide +kernel
  have he (w : CompleteWord 2) :
      (denominator : ℝ) ^ 4 * (x c z w : ℝ) = (ReleasedInterior.integerProfile 0 27 (z + 1) ⟨1, c⟩ w : ℝ) := by
    exact_mod_cast hid c z hz w
  simp_rw [he] at h
  change (denominator : ℝ) ^ 4 * ((boundNumerator c z : ℝ) / 1000000000000) ≤ _
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
