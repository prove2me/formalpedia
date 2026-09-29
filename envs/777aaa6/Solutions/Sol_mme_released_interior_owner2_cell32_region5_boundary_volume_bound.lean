-- Prove2me | solution 1 for mme_released_interior_owner2_cell32_region5_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T16:34:43.035368+00:00
-- url     : https://prove2.me/submissions/60919445-daa9-463c-bf62-7af51d3a1e84

import Theorems.Thm_mme_rational_boundary_volume_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed
open MME.CompleteSplit MME.RecursiveYZ MME.RecursiveYZ.Boundary

private abbrev Split := ReleasedInterior.Split 32
private def rowIndex (c : Split) (z : Fin 3) : ℕ :=
  3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def massNumerator (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 3137307861607395128043646636128, 0, 68287478239943673199912706727744, 0, 3137307861607395128043646636128, 0, 0]),
    (157, [0, 0, 1497726533946045813603207140594160, 0, 28780943204782330966409585718811680, 0, 1497726533946045813603207140594160, 0, 0]),
    (182, [0, 0, 1216150926945723912249971775602496, 0, 29344094418782974769116056448795008, 0, 1216150926945723912249971775602496, 0, 0]),
    (229, [0, 4661189882128578813888000000000000, 0, 4661189882128578813888000000000000, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 4132175288962460293776000000000000, 0, 4132175288962460293776000000000000, 0]),
    (301, [74562093963158463456000000000000, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 74562093963158463456000000000000])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def logScale (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (157, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (182, [0, 0, 5, 0, 1, 0, 5, 0, 0]),
    (229, [0, 1, 0, 1, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 1, 0, 1, 0]),
    (301, [0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def lowerMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 3168267190999, 0, 87905839185, 0, 3168267190999, 0, 0]),
    (157, [0, 0, 3054775444280, 0, 99010284755, 0, 3054775444280, 0, 0]),
    (182, [0, 0, 3263032865206, 0, 79632444881, 0, 3263032865206, 0, 0]),
    (229, [0, 693147180560, 0, 693147180560, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 693147180560, 0, 693147180560, 0]),
    (301, [0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def upperMagnitude (c : Split) (z : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((([(36, [0, 0, 3168267190998, 0, 87905839184, 0, 3168267190998, 0, 0]),
    (157, [0, 0, 3054775444279, 0, 99010284754, 0, 3054775444279, 0, 0]),
    (182, [0, 0, 3263032865205, 0, 79632444880, 0, 3263032865205, 0, 0]),
    (229, [0, 693147180559, 0, 693147180559, 0, 0, 0, 0, 0]),
    (242, [0, 0, 0, 0, 0, 693147180559, 0, 693147180559, 0]),
    (301, [0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (302, [0, 0, 0, 0, 0, 0, 0, 0, 0])] : List (ℕ × List ℕ)).find? (fun p => p.1 == rowIndex c z)).getD
    (0, [])).2.getD (wordIndex w) 0

private def boundNumerator (c : Split) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 245691440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104642328157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104728418995, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21465572676, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19029370443, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (rowIndex c z) 0

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
    (c : ReleasedInterior.Split 32) (z : Fin 3) (hz : (c.val z).val = 0) :
    (denominator : ℝ) ^ 4 *
      ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 245691440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104642328157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104728418995, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21465572676, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19029370443, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD
        (3 * (25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val) + z.val) 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (ReleasedInterior.integerProfile 2 32 (z + 1) ⟨5, c⟩ w : ℝ)) +
        (∑ w, (ReleasedInterior.integerProfile 2 32 (z + 1) ⟨5, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ c z w, 0 ≤ x c z w := by decide +kernel
  have hcert : ∀ c z, bound c z ≤
      (∑ w, x c z w) * (-(∑ w, (x c z w / ∑ v, x c z v) * upper c z w)) +
        (∑ w, x c z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x c z) (hx c z) ones
    (lower c z) (upper c z) (log_bounds c z) (bound c z) (hcert c z)
    ((denominator : ℝ) ^ 4) (by positivity)
  have hid : ∀ (c : Split) (z : Fin 3), (c.val z).val = 0 → ∀ w,
      (denominator : ℚ) ^ 4 * x c z w = (ReleasedInterior.integerProfile 2 32 (z + 1) ⟨5, c⟩ w : ℚ) := by
    decide +kernel
  have he (w : CompleteWord 2) :
      (denominator : ℝ) ^ 4 * (x c z w : ℝ) = (ReleasedInterior.integerProfile 2 32 (z + 1) ⟨5, c⟩ w : ℝ) := by
    exact_mod_cast hid c z hz w
  simp_rw [he] at h
  change (denominator : ℝ) ^ 4 * ((boundNumerator c z : ℝ) / 1000000000000) ≤ _
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
