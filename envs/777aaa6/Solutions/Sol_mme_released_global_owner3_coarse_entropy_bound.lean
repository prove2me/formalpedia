-- Prove2me | solution 1 for mme_released_global_owner3_coarse_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:14.086605+00:00
-- url     : https://prove2.me/submissions/14b29ba2-0cb3-4dec-93d9-7c6a1b8d902c

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_global_profile_data

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

private def massNumerator (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![23084218864, 114209204969, 289429116615, 352365922980, 190158912790, 29041355021, 1677907713, 33241227, 119821], ![23074225017, 113875828100, 289597846017, 352758173063, 190080270652, 28920701043, 1659706193, 33130259, 119656], ![22770753126, 113628044885, 289860147437, 353277718467, 189975876177, 28813507893, 1640784390, 33046877, 120748]] : Fin 3 → Fin 9 → ℕ) i j

private def logScale (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23]] : Fin 3 → Fin 9 → ℕ) i j

private def lowerMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768606060980, 2169723381077, 1239844859566, 1043085089426, 1659895173290, 3539034429612, 6390207670662, 10311719675301, 15937266874474], ![3769039084553, 2172646651420, 1239262056285, 1041972518956, 1660308818925, 3543197641218, 6401114684448, 10315063523996, 15938644877590], ![3782278324092, 2174824929176, 1238356722539, 1040500793498, 1660858182373, 3546910977736, 6412580864904, 10317583489324, 15929560107698]] : Fin 3 → Fin 9 → ℕ) i j

private def upperMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768606060979, 2169723381076, 1239844859565, 1043085089425, 1659895173289, 3539034429611, 6390207670661, 10311719675300, 15937266874473], ![3769039084552, 2172646651419, 1239262056284, 1041972518955, 1660308818924, 3543197641217, 6401114684447, 10315063523995, 15938644877589], ![3782278324091, 2174824929175, 1238356722538, 1040500793497, 1660858182372, 3546910977735, 6412580864903, 10317583489323, 15929560107697]] : Fin 3 → Fin 9 → ℕ) i j

private def alphaQ (c : Shape) : ℚ :=
  (alpha 3 ⟨shapeIndex c % 45, Nat.mod_lt _ (by decide)⟩ : ℚ) / 1000000000000
private def x (i : Fin 3) (j : Fin 9) : ℚ := (massNumerator i j : ℚ) / 1000000000000
private def lower (i : Fin 3) (j : Fin 9) : ℚ := -(lowerMagnitude i j : ℚ) / 1000000000000
private def upper (i : Fin 3) (j : Fin 9) : ℚ := -(upperMagnitude i j : ℚ) / 1000000000000
private def bound (i : Fin 3) : ℚ := ((![1490681631, 1489862863, 1488368925] : Fin 3 → ℕ) i : ℚ) / 1000000000

private theorem log_bounds (i : Fin 3) (j : Fin 9)
    (hp : 0 < x i j / ∑ v, x i v) :
    (lower i j : ℝ) ≤ Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ∧
      Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ≤ (upper i j : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale i j) 16
  all_goals revert i j; decide +kernel

/-- Each directional coarse entropy of the actual released outer profile
has an explicit rational lower bound. -/
theorem solution (i : Fin 3) :
    (((![1490681631, 1489862863, 1488368925] : Fin 3 → ℕ) i : ℝ) / 1000000000) ≤
      (profile 3).coarse i 0 := by
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
      (coarseCounts 3 c : ℝ) / (denominator : ℝ) ^ 5 := by
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
        (fun c ↦ (coarseCounts 3 c : ℝ) / (denominator : ℝ) ^ 5) j := by
    rw [hid]
    push_cast
    unfold mme_modern_marginal
    exact Finset.sum_congr rfl (fun c _ ↦ ha c.val)
  simp_rw [he] at hl
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    GlobalCW.EntropyProfile.coarse, profile] using h.trans hl


#print axioms solution
