-- Prove2me | solution 1 for mme_released_global_owner4_coarse_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:15.823606+00:00
-- url     : https://prove2.me/submissions/7be99cad-ff81-48a6-ae31-90c91554a524

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_global_profile_data

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

private def massNumerator (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![23084076289, 114208161993, 289431149249, 352366504291, 190158128371, 29040656157, 1677893564, 33310157, 119929], ![23073656383, 113875631401, 289599598993, 352758014859, 190079497625, 28920610917, 1659731621, 33138470, 119731], ![22770641865, 113626909104, 289861498290, 353277312872, 189975724445, 28814039028, 1640674352, 33079145, 120899]] : Fin 3 → Fin 9 → ℕ) i j

private def logScale (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23]] : Fin 3 → Fin 9 → ℕ) i j

private def lowerMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768612237296, 2169732513273, 1239837836683, 1043083439691, 1659899298370, 3539058494343, 6390216103224, 10309648192471, 15936365935935], ![3769063728545, 2172648378733, 1239256003165, 1041972967433, 1660312885778, 3543200757538, 6401099363781, 10314815714805, 15938018277127], ![3782283210240, 2174834924831, 1238352062189, 1040501941590, 1660858981064, 3546892544364, 6412647931418, 10316607534576, 15928310350659]] : Fin 3 → Fin 9 → ℕ) i j

private def upperMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768612237295, 2169732513272, 1239837836682, 1043083439690, 1659899298369, 3539058494342, 6390216103223, 10309648192470, 15936365935934], ![3769063728544, 2172648378732, 1239256003164, 1041972967432, 1660312885777, 3543200757537, 6401099363780, 10314815714804, 15938018277126], ![3782283210239, 2174834924830, 1238352062188, 1040501941589, 1660858981063, 3546892544363, 6412647931417, 10316607534575, 15928310350658]] : Fin 3 → Fin 9 → ℕ) i j

private def alphaQ (c : Shape) : ℚ :=
  (alpha 4 ⟨shapeIndex c % 45, Nat.mod_lt _ (by decide)⟩ : ℚ) / 1000000000000
private def x (i : Fin 3) (j : Fin 9) : ℚ := (massNumerator i j : ℚ) / 1000000000000
private def lower (i : Fin 3) (j : Fin 9) : ℚ := -(lowerMagnitude i j : ℚ) / 1000000000000
private def upper (i : Fin 3) (j : Fin 9) : ℚ := -(upperMagnitude i j : ℚ) / 1000000000000
private def bound (i : Fin 3) : ℚ := ((![1490678804, 1489860946, 1488368546] : Fin 3 → ℕ) i : ℚ) / 1000000000

private theorem log_bounds (i : Fin 3) (j : Fin 9)
    (hp : 0 < x i j / ∑ v, x i v) :
    (lower i j : ℝ) ≤ Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ∧
      Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ≤ (upper i j : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale i j) 16
  all_goals revert i j; decide +kernel

/-- Each directional coarse entropy of the actual released outer profile
has an explicit rational lower bound. -/
theorem solution (i : Fin 3) :
    (((![1490678804, 1489860946, 1488368546] : Fin 3 → ℕ) i : ℝ) / 1000000000) ≤
      (profile 4).coarse i 0 := by
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
      (coarseCounts 4 c : ℝ) / (denominator : ℝ) ^ 5 := by
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
        (fun c ↦ (coarseCounts 4 c : ℝ) / (denominator : ℝ) ^ 5) j := by
    rw [hid]
    push_cast
    unfold mme_modern_marginal
    exact Finset.sum_congr rfl (fun c _ ↦ ha c.val)
  simp_rw [he] at hl
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    GlobalCW.EntropyProfile.coarse, profile] using h.trans hl


#print axioms solution
