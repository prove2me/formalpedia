-- Prove2me | solution 1 for mme_released_global_owner1_coarse_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:11.695209+00:00
-- url     : https://prove2.me/submissions/65519f37-e1dd-4047-9f0c-e161e77cfe8f

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_global_profile_data

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

private def massNumerator (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![23084730427, 114207684703, 289431543510, 352365823494, 190158295118, 29040602464, 1677895669, 33304688, 119927], ![23074493752, 113875467179, 289598989021, 352757102868, 190080705926, 28920265772, 1659713678, 33142078, 119726], ![22770280155, 113626801238, 289860368551, 353278502325, 189976452515, 28813779710, 1640625398, 33069231, 120877]] : Fin 3 → Fin 9 → ℕ) i j

private def logScale (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23]] : Fin 3 → Fin 9 → ℕ) i j

private def lowerMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768583900501, 2169736692405, 1239836474491, 1043085371763, 1659898421484, 3539060343236, 6390214848675, 10309812390106, 15936382612608], ![3769027438076, 2172649820851, 1239258109427, 1041975552753, 1660306528979, 3543212691831, 6401110174624, 10314706844251, 15938060038279], ![3782299095294, 2174835874131, 1238355959710, 1040498574686, 1660855148634, 3546901544114, 6412677769594, 10316907284946, 15928492337292]] : Fin 3 → Fin 9 → ℕ) i j

private def upperMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768583900500, 2169736692404, 1239836474490, 1043085371762, 1659898421483, 3539060343235, 6390214848674, 10309812390105, 15936382612607], ![3769027438075, 2172649820850, 1239258109426, 1041975552752, 1660306528978, 3543212691830, 6401110174623, 10314706844250, 15938060038278], ![3782299095293, 2174835874130, 1238355959709, 1040498574685, 1660855148633, 3546901544113, 6412677769593, 10316907284945, 15928492337291]] : Fin 3 → Fin 9 → ℕ) i j

private def alphaQ (c : Shape) : ℚ :=
  (alpha 1 ⟨shapeIndex c % 45, Nat.mod_lt _ (by decide)⟩ : ℚ) / 1000000000000
private def x (i : Fin 3) (j : Fin 9) : ℚ := (massNumerator i j : ℚ) / 1000000000000
private def lower (i : Fin 3) (j : Fin 9) : ℚ := -(lowerMagnitude i j : ℚ) / 1000000000000
private def upper (i : Fin 3) (j : Fin 9) : ℚ := -(upperMagnitude i j : ℚ) / 1000000000000
private def bound (i : Fin 3) : ℚ := ((![1490680056, 1489862745, 1488366655] : Fin 3 → ℕ) i : ℚ) / 1000000000

private theorem log_bounds (i : Fin 3) (j : Fin 9)
    (hp : 0 < x i j / ∑ v, x i v) :
    (lower i j : ℝ) ≤ Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ∧
      Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ≤ (upper i j : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale i j) 16
  all_goals revert i j; decide +kernel

/-- Each directional coarse entropy of the actual released outer profile
has an explicit rational lower bound. -/
theorem solution (i : Fin 3) :
    (((![1490680056, 1489862745, 1488366655] : Fin 3 → ℕ) i : ℝ) / 1000000000) ≤
      (profile 1).coarse i 0 := by
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
      (coarseCounts 1 c : ℝ) / (denominator : ℝ) ^ 5 := by
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
        (fun c ↦ (coarseCounts 1 c : ℝ) / (denominator : ℝ) ^ 5) j := by
    rw [hid]
    push_cast
    unfold mme_modern_marginal
    exact Finset.sum_congr rfl (fun c _ ↦ ha c.val)
  simp_rw [he] at hl
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    GlobalCW.EntropyProfile.coarse, profile] using h.trans hl


#print axioms solution
