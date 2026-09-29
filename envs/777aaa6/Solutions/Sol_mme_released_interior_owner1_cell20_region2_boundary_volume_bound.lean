-- Prove2me | solution 1 for mme_released_interior_owner1_cell20_region2_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T11:08:45.252872+00:00
-- url     : https://prove2.me/submissions/fbfc0d12-8475-4dbe-b755-de54a3c47a44

import Theorems.Thm_mme_rational_boundary_volume_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed
open MME.CompleteSplit MME.RecursiveYZ MME.RecursiveYZ.Boundary

private abbrev Split := ReleasedInterior.Split 20
private def rowIndex (c : Split) (z : Fin 3) : ℕ :=
  3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def massNumerator (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(24, [0, 2333864285852526319534000000000000, 0, 2333864285852526319534000000000000, 0, 0, 0, 0, 0]),
    (36, [0, 0, 3885532443895380516977711389986352, 0, 60499316732326084808632577220027296, 0, 3885532443895380516977711389986352, 0, 0]),
    (48, [0, 0, 0, 0, 0, 2541919066315678991368000000000000, 0, 2541919066315678991368000000000000, 0]),
    (85, [0, 0, 0, 0, 0, 343838755785878285199000000000000, 0, 343838755785878285199000000000000, 0]),
    (122, [0, 343838755785878285199000000000000, 0, 343838755785878285199000000000000, 0, 0, 0, 0, 0]),
    (157, [0, 0, 257793244250513456226719017447568, 0, 4568251644130331070282561965104864, 0, 257793244250513456226719017447568, 0, 0]),
    (182, [0, 0, 252078636625053660934651638060812, 0, 4163571298454945317198696723878376, 0, 252078636625053660934651638060812, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def logScale (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(24, [0, 1, 0, 1, 0, 0, 0, 0, 0]),
    (36, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (48, [0, 0, 0, 0, 0, 1, 0, 1, 0]),
    (85, [0, 0, 0, 0, 0, 1, 0, 1, 0]),
    (122, [0, 1, 0, 1, 0, 0, 0, 0, 0]),
    (157, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (182, [0, 0, 5, 0, 1, 0, 5, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def lowerMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(24, [0, 693147180560, 0, 693147180560, 0, 0, 0, 0, 0]),
    (36, [0, 0, 2866215995656, 0, 120843949988, 0, 2866215995656, 0, 0]),
    (48, [0, 0, 0, 0, 0, 693147180560, 0, 693147180560, 0]),
    (85, [0, 0, 0, 0, 0, 693147180560, 0, 693147180560, 0]),
    (122, [0, 693147180560, 0, 693147180560, 0, 0, 0, 0, 0]),
    (157, [0, 0, 2981663908446, 0, 106935954929, 0, 2981663908446, 0, 0]),
    (182, [0, 0, 2918686756190, 0, 114299374950, 0, 2918686756190, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def upperMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(24, [0, 693147180559, 0, 693147180559, 0, 0, 0, 0, 0]),
    (36, [0, 0, 2866215995655, 0, 120843949987, 0, 2866215995655, 0, 0]),
    (48, [0, 0, 0, 0, 0, 693147180559, 0, 693147180559, 0]),
    (85, [0, 0, 0, 0, 0, 693147180559, 0, 693147180559, 0]),
    (122, [0, 693147180559, 0, 693147180559, 0, 0, 0, 0, 0]),
    (157, [0, 0, 2981663908445, 0, 106935954928, 0, 2981663908445, 0, 0]),
    (182, [0, 0, 2918686756189, 0, 114299374949, 0, 2918686756189, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def boundNumerator (c : Split) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10747842227, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 224324314940, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11705969899, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1583435986, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1583435986, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16730450755, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15349389751, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (rowIndex c z) 0

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
    (c : ReleasedInterior.Split 20) (z : Fin 3) (hz : (c.val z).val = 0) :
    (denominator : ℝ) ^ 4 *
      ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10747842227, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 224324314940, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11705969899, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1583435986, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1583435986, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16730450755, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15349389751, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
        (3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val) 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 20 (z + 1) ⟨2, c⟩ w : ℝ)) +
        (∑ w, (ReleasedInterior.integerProfile 1 20 (z + 1) ⟨2, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ c z w, 0 ≤ x c z w := by decide +kernel
  have hcert : ∀ c z, bound c z ≤
      (∑ w, x c z w) * (-(∑ w, (x c z w / ∑ v, x c z v) * upper c z w)) +
        (∑ w, x c z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x c z) (hx c z) ones
    (lower c z) (upper c z) (log_bounds c z) (bound c z) (hcert c z)
    ((denominator : ℝ) ^ 4) (by positivity)
  have hid : ∀ (c : Split) (z : Fin 3), (c.val z).val = 0 → ∀ w,
      (denominator : ℚ) ^ 4 * x c z w = (ReleasedInterior.integerProfile 1 20 (z + 1) ⟨2, c⟩ w : ℚ) := by
    decide +kernel
  have he (w : CompleteWord 2) :
      (denominator : ℝ) ^ 4 * (x c z w : ℝ) = (ReleasedInterior.integerProfile 1 20 (z + 1) ⟨2, c⟩ w : ℝ) := by
    exact_mod_cast hid c z hz w
  simp_rw [he] at h
  change (denominator : ℝ) ^ 4 * ((boundNumerator c z : ℝ) / 1000000000000) ≤ _
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
