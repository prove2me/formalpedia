-- Prove2me | solution 1 for mme_released_global_owner2_coarse_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:13.176877+00:00
-- url     : https://prove2.me/submissions/7d3b3643-4323-45f3-8646-24bd41021697

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_global_profile_data

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

private def massNumerator (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![23085120448, 114206875978, 289430446981, 352366671282, 190158561853, 29040973473, 1677886867, 33343025, 120093], ![23075305548, 113875810408, 289598596955, 352755960858, 190081284693, 28920019484, 1659786671, 33115773, 119610], ![22769765702, 113627062839, 289861161586, 353277988935, 189976860356, 28813238202, 1640754758, 33046859, 120763]] : Fin 3 → Fin 9 → ℕ) i j

private def logScale (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23], ![6, 4, 2, 2, 3, 6, 10, 15, 23]] : Fin 3 → Fin 9 → ℕ) i j

private def lowerMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768567005450, 2169743773608, 1239840263059, 1043082965778, 1659897018785, 3539047567790, 6390220094545, 10308661952904, 15934999394322], ![3768992257165, 2172646806782, 1239259463251, 1041978790142, 1660303484135, 3543221207972, 6401066196318, 10315500863404, 15939029386886], ![3782321688727, 2174833571851, 1238353223793, 1040500027903, 1660853001839, 3546920337660, 6412598924722, 10317584034005, 15929435889754]] : Fin 3 → Fin 9 → ℕ) i j

private def upperMagnitude (i : Fin 3) (j : Fin 9) : ℕ :=
  (![![3768567005449, 2169743773607, 1239840263058, 1043082965777, 1659897018784, 3539047567789, 6390220094544, 10308661952903, 15934999394321], ![3768992257164, 2172646806781, 1239259463250, 1041978790141, 1660303484134, 3543221207971, 6401066196317, 10315500863403, 15939029386885], ![3782321688726, 2174833571850, 1238353223792, 1040500027902, 1660853001838, 3546920337659, 6412598924721, 10317584034004, 15929435889753]] : Fin 3 → Fin 9 → ℕ) i j

private def alphaQ (c : Shape) : ℚ :=
  (alpha 2 ⟨shapeIndex c % 45, Nat.mod_lt _ (by decide)⟩ : ℚ) / 1000000000000
private def x (i : Fin 3) (j : Fin 9) : ℚ := (massNumerator i j : ℚ) / 1000000000000
private def lower (i : Fin 3) (j : Fin 9) : ℚ := -(lowerMagnitude i j : ℚ) / 1000000000000
private def upper (i : Fin 3) (j : Fin 9) : ℚ := -(upperMagnitude i j : ℚ) / 1000000000000
private def bound (i : Fin 3) : ℚ := ((![1490681393, 1489865157, 1488365079] : Fin 3 → ℕ) i : ℚ) / 1000000000

private theorem log_bounds (i : Fin 3) (j : Fin 9)
    (hp : 0 < x i j / ∑ v, x i v) :
    (lower i j : ℝ) ≤ Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ∧
      Real.log ((x i j / ∑ v, x i v : ℚ) : ℝ) ≤ (upper i j : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale i j) 16
  all_goals revert i j; decide +kernel

/-- Each directional coarse entropy of the actual released outer profile
has an explicit rational lower bound. -/
theorem solution (i : Fin 3) :
    (((![1490681393, 1489865157, 1488365079] : Fin 3 → ℕ) i : ℝ) / 1000000000) ≤
      (profile 2).coarse i 0 := by
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
      (coarseCounts 2 c : ℝ) / (denominator : ℝ) ^ 5 := by
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
        (fun c ↦ (coarseCounts 2 c : ℝ) / (denominator : ℝ) ^ 5) j := by
    rw [hid]
    push_cast
    unfold mme_modern_marginal
    exact Finset.sum_congr rfl (fun c _ ↦ ha c.val)
  simp_rw [he] at hl
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    GlobalCW.EntropyProfile.coarse, profile] using h.trans hl


#print axioms solution
