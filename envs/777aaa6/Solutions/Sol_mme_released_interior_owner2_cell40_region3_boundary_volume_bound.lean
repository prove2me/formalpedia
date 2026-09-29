-- Prove2me | solution 1 for mme_released_interior_owner2_cell40_region3_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T16:46:49.918172+00:00
-- url     : https://prove2.me/submissions/aabde9ee-776d-4301-b3cb-85fa80bfb875

import Theorems.Thm_mme_rational_boundary_volume_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed
open MME.CompleteSplit MME.RecursiveYZ MME.RecursiveYZ.Boundary

private abbrev Split := ReleasedInterior.Split 40
private def rowIndex (c : Split) (z : Fin 3) : ℕ :=
  3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def massNumerator (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(229, [0, 63446630565050080717594500000000000, 0, 63446630565050080717594500000000000, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 63446630565050080717594500000000000, 0, 63446630565050080717594500000000000, 0]),
    (301, [39447105050899838564811000000000000, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 39447105050899838564811000000000000])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def logScale (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(229, [0, 1, 0, 1, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 1, 0, 1, 0]),
    (301, [0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def lowerMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(229, [0, 693147180560, 0, 693147180560, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 693147180560, 0, 693147180560, 0]),
    (301, [0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def upperMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(229, [0, 693147180559, 0, 693147180559, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 693147180559, 0, 693147180559, 0]),
    (301, [0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def boundNumerator (c : Split) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 292182531479, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 292182531479, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (rowIndex c z) 0

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
    (c : ReleasedInterior.Split 40) (z : Fin 3) (hz : (c.val z).val = 0) :
    (denominator : ℝ) ^ 4 *
      ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 292182531479, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 292182531479, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
        (3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val) 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (ReleasedInterior.integerProfile 2 40 (z + 1) ⟨3, c⟩ w : ℝ)) +
        (∑ w, (ReleasedInterior.integerProfile 2 40 (z + 1) ⟨3, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ c z w, 0 ≤ x c z w := by decide +kernel
  have hcert : ∀ c z, bound c z ≤
      (∑ w, x c z w) * (-(∑ w, (x c z w / ∑ v, x c z v) * upper c z w)) +
        (∑ w, x c z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x c z) (hx c z) ones
    (lower c z) (upper c z) (log_bounds c z) (bound c z) (hcert c z)
    ((denominator : ℝ) ^ 4) (by positivity)
  have hid : ∀ (c : Split) (z : Fin 3), (c.val z).val = 0 → ∀ w,
      (denominator : ℚ) ^ 4 * x c z w = (ReleasedInterior.integerProfile 2 40 (z + 1) ⟨3, c⟩ w : ℚ) := by
    decide +kernel
  have he (w : CompleteWord 2) :
      (denominator : ℝ) ^ 4 * (x c z w : ℝ) = (ReleasedInterior.integerProfile 2 40 (z + 1) ⟨3, c⟩ w : ℝ) := by
    exact_mod_cast hid c z hz w
  simp_rw [he] at h
  change (denominator : ℝ) ^ 4 * ((boundNumerator c z : ℝ) / 1000000000000) ≤ _
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
