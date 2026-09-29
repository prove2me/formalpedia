-- Prove2me | solution 1 for mme_released_global_owner0_coarse_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:47.627337+00:00
-- url     : https://prove2.me/submissions/5821724d-d1a0-4a0b-8fdd-0e552c1a3e3e

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_global_profile_data

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

private def massNumerator (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![23084257637, 114208299690, 289429449502, 352366118755, 190159837065, 29040696820, 1677887613, 33332879, 120039], ![23074029039, 113875665016, 289597919844, 352758823574, 190081346806, 28919256540, 1659716070, 33123453, 119658], ![22772318105, 113625676988, 289859695296, 353279584409, 189975324446, 28813540565, 1640730185, 33009241, 120765]] : Fin 3 → Fin 9 → ℕ) i j

private def logScale (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23]] : Fin 3 → Fin 9 → ℕ) i j

private def lowerMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768604381349, 2169731307606, 1239843709417, 1043084533825, 1659890312762, 3539057094135, 6390219649939, 10308966290738, 15935449146966], ![3769047577962, 2172648083543, 1239261801356, 1041970674887, 1660303157364, 3543247589491, 6401108733412, 10315268976636, 15938628163148], ![3782209598863, 2174845768413, 1238358282400, 1040495511713, 1660861086593, 3546909843824, 6412613901478, 10318723005396, 15929419328527]] : Fin 3 → Fin 9 → ℕ) i j

private def upperMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768604381348, 2169731307605, 1239843709416, 1043084533824, 1659890312761, 3539057094134, 6390219649938, 10308966290737, 15935449146965], ![3769047577961, 2172648083542, 1239261801355, 1041970674886, 1660303157363, 3543247589490, 6401108733411, 10315268976635, 15938628163147], ![3782209598862, 2174845768412, 1238358282399, 1040495511712, 1660861086592, 3546909843823, 6412613901477, 10318723005395, 15929419328526]] : Fin 3 → Fin 9 → ℕ) i j

private def alphaQ (c : Shape) : ℚ :=
  (alpha 0 ⟨shapeIndex c % 45, Nat.mod_lt _ (by decide)⟩ : ℚ) / 1000000000000
private def x (i : Fin 3) (j : Fin 9) : ℚ := (massNumerator i j : ℚ) / 1000000000000
private def lower (i : Fin 3) (j : Fin 9) : ℚ := -(lowerMagnitude i j : ℚ) / 1000000000000
private def upper (i : Fin 3) (j : Fin 9) : ℚ := -(upperMagnitude i j : ℚ) / 1000000000000
private def bound (i : Fin 3) : ℚ := ((![1490680455, 1489859201, 1488369539] : Fin 3 → ℕ) i : ℚ) / 1000000000

private theorem log_bounds (i : Fin 3) (j : Fin 9)
    (hp : 0 < x i j / ∑ v, x i v) :
    (lower i j : ℝ) ≤ Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ∧
      Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ≤ (upper i j : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale i j) 16
  all_goals revert i j; decide +kernel

/-- Each directional coarse entropy of the actual released outer profile
has an explicit rational lower bound. -/
theorem solution (i : Fin 3) :
    (((![1490680455, 1489859201, 1488369539] : Fin 3 → ℕ) i : ℝ) / 1000000000) ≤
      (profile 0).coarse i 0 := by
  have hx : ∀ i j, 0 ≤ x i j := by decide +kernel
  have hc : ∀ i, bound i ≤ (∑ j, x i j) * (-(∑ j, (x i j / ∑ v, x i v) * upper i j)) := by
    decide +kernel
  have h := (Rat.cast_le (K := ℝ)).2 (hc i)
  have hl := (mme_rational_mass_entropy_log_bounds (x i) (hx i)
    (lower i) (upper i) (log_bounds i)).1
  have hid : ∀ i j, x i j =
      ∑ c : {c : Shape // c.val i = j},
        alphaQ c.val := by
    decide +kernel
  have ha (c : Shape) : (alphaQ c : ℝ) =
      (coarseCounts 0 c : ℝ) / (denominator : ℝ) ^ 5 := by
    have hs : (shapeEquiv.symm c).val = shapeIndex c := by
      obtain ⟨s, rfl⟩ := shapeEquiv.surjective c
      rw [Equiv.symm_apply_apply]
      exact ((by decide +kernel : ∀ s : Fin 45, shapeIndex (shape s) = s.val) s).symm
    have hidx : (⟨shapeIndex c % 45, Nat.mod_lt _ (by decide)⟩ : Fin 45) =
        shapeEquiv.symm c := by
      apply Fin.ext
      simp only [← hs, Nat.mod_eq_of_lt (shapeEquiv.symm c).isLt]
    simp only [alphaQ, hidx, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
      coarseCounts, Nat.cast_mul, Nat.cast_pow]
    norm_num [denominator]
    ring
  have he (j : Fin 9) : (x i j : ℝ) =
      mme_modern_marginal (fun c : Shape ↦ c.val i)
        (fun c ↦ (coarseCounts 0 c : ℝ) / (denominator : ℝ) ^ 5) j := by
    rw [hid]
    push_cast
    unfold mme_modern_marginal
    exact Finset.sum_congr rfl (fun c _ ↦ ha c.val)
  simp_rw [he] at hl
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    GlobalCW.EntropyProfile.coarse, profile] using h.trans hl


#print axioms solution
