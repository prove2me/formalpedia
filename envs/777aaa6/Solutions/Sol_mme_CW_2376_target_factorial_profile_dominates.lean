-- Prove2me | solution 1 for mme_CW_2376_target_factorial_profile_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:12:26.951385+00:00
-- url     : https://prove2.me/submissions/4433788c-8cf5-48f3-af8b-a4ec1ac22733

import Theorems.Thm_mme_CW_2376_target_product_weight_identity

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 300000

private theorem nat_pow_mul_factorial_mode (w a : ℕ) :
    w ^ a * w.factorial ≤ w ^ w * a.factorial := by
  rcases le_total a w with haw | hwa
  · have hdesc : w.factorial ≤ a.factorial * w ^ (w - a) := by
      have hfac :=
        Nat.factorial_mul_descFactorial (n := w) (k := w - a)
          (Nat.sub_le w a)
      calc
        w.factorial = a.factorial * w.descFactorial (w - a) := by
          simpa only [Nat.sub_sub_self haw] using hfac.symm
        _ ≤ a.factorial * w ^ (w - a) :=
          Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow w (w - a))
    calc
      w ^ a * w.factorial ≤ w ^ a * (a.factorial * w ^ (w - a)) :=
        Nat.mul_le_mul_left _ hdesc
      _ = (w ^ a * w ^ (w - a)) * a.factorial := by ac_rfl
      _ = w ^ (a + (w - a)) * a.factorial := by rw [Nat.pow_add]
      _ = w ^ w * a.factorial := by rw [Nat.add_sub_of_le haw]
  · have htail : w.factorial * w ^ (a - w) ≤ a.factorial :=
      Nat.factorial_mul_pow_sub_le_factorial hwa
    calc
      w ^ a * w.factorial =
          w ^ w * (w.factorial * w ^ (a - w)) := by
            calc
              w ^ a * w.factorial =
                  (w ^ w * w ^ (a - w)) * w.factorial := by
                    rw [← Nat.pow_add, Nat.add_sub_of_le hwa]
              _ = w ^ w * (w.factorial * w ^ (a - w)) := by ac_rfl
      _ ≤ w ^ w * a.factorial := Nat.mul_le_mul_left _ htail

private theorem prod_pow_by_fiber_finset
    {alpha beta : Type} [Fintype beta] [DecidableEq beta]
    (s : Finset alpha) (g : alpha → beta) (q : beta → ℕ)
    (f : alpha → ℕ) :
    (∏ x ∈ s, q (g x) ^ f x) =
      ∏ y, q y ^ (∑ x ∈ s, if g x = y then f x else 0) := by
  calc
    (∏ x ∈ s, q (g x) ^ f x) =
        ∏ x ∈ s, ∏ y, q y ^ (if g x = y then f x else 0) := by
      apply Finset.prod_congr rfl
      intro x hx
      simp
    _ = ∏ y, ∏ x ∈ s, q y ^ (if g x = y then f x else 0) := by
      exact Finset.prod_comm
    _ = ∏ y, q y ^ (∑ x ∈ s, if g x = y then f x else 0) := by
      apply Finset.prod_congr rfl
      intro y hy
      exact Finset.prod_pow_eq_pow_sum _ _ _

private theorem prod_mul_pow_split_finset
    {alpha : Type} (s : Finset alpha)
    (c : ℕ) (b f : alpha → ℕ) :
    (∏ x ∈ s, (c * b x) ^ f x) =
      c ^ (∑ x ∈ s, f x) * ∏ x ∈ s, b x ^ f x := by
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_pow_eq_pow_sum _ _ _

private theorem prod_prod_pow_swap_finset
    {alpha beta : Type} [Fintype beta]
    (s : Finset alpha) (q : alpha → beta → ℕ) (f : alpha → ℕ) :
    (∏ x ∈ s, (∏ y, q x y) ^ f x) =
      ∏ y, ∏ x ∈ s, q x y ^ f x := by
  calc
    (∏ x ∈ s, (∏ y, q x y) ^ f x) =
        ∏ x ∈ s, ∏ y, q x y ^ f x := by
      apply Finset.prod_congr rfl
      intro x hx
      exact (Finset.prod_pow Finset.univ (f x) (q x)).symm
    _ = ∏ y, ∏ x ∈ s, q x y ^ f x := Finset.prod_comm

/-- The optimized target table minimizes the product of factorial
denominators among all supported joint tables with the same three marginals. -/
theorem solution
    (m : ℕ) (hm : 0 < m) (a : (Fin 3 → Fin 5) → ℕ)
    (ha : ∀ i : Fin 3, ∀ r : Fin 5,
      (∑ sigma ∈ cw2376TargetJointTypes,
        if sigma i = r then a sigma else 0) =
      ∑ sigma ∈ cw2376TargetJointTypes,
        if sigma i = r then cw2376ProfileMultiplicity m sigma else 0)
    (htotal : (∑ sigma ∈ cw2376TargetJointTypes, a sigma) =
      ∑ sigma ∈ cw2376TargetJointTypes,
        cw2376ProfileMultiplicity m sigma) :
    (∏ sigma ∈ cw2376TargetJointTypes,
        (cw2376ProfileMultiplicity m sigma).factorial) ≤
      ∏ sigma ∈ cw2376TargetJointTypes, (a sigma).factorial := by
  have hw : ∀ sigma ∈ cw2376TargetJointTypes,
      0 < cw2376ProfileMultiplicity m sigma := by
    intro sigma hsigma
    have hfactor := mme_CW_2376_target_product_weight_identity m sigma hsigma
    have hgrade_one (r : Fin 5) :
        0 < cw2376DominanceGradeWeight r := by
      fin_cases r <;> norm_num [cw2376DominanceGradeWeight]
    have hgrade : 0 < ∏ i : Fin 3,
        cw2376DominanceGradeWeight (sigma i) := by
      apply Finset.prod_pos
      intro i hi
      exact hgrade_one (sigma i)
    have hright : 0 < m * ∏ i : Fin 3,
        cw2376DominanceGradeWeight (sigma i) := Nat.mul_pos hm hgrade
    have hleft : 0 < cw2376DominanceScale *
        cw2376ProfileMultiplicity m sigma := by
      rw [hfactor]
      exact hright
    exact Nat.pos_of_mul_pos_left hleft
  have hmode (i : Fin 3) :
      (∏ sigma ∈ cw2376TargetJointTypes,
          cw2376DominanceGradeWeight (sigma i) ^ a sigma) =
        ∏ sigma ∈ cw2376TargetJointTypes,
          cw2376DominanceGradeWeight (sigma i) ^
            cw2376ProfileMultiplicity m sigma := by
    calc
      (∏ sigma ∈ cw2376TargetJointTypes,
          cw2376DominanceGradeWeight (sigma i) ^ a sigma) =
          ∏ r, cw2376DominanceGradeWeight r ^
            (∑ sigma ∈ cw2376TargetJointTypes,
              if sigma i = r then a sigma else 0) :=
        prod_pow_by_fiber_finset cw2376TargetJointTypes
          (fun sigma => sigma i)
          cw2376DominanceGradeWeight a
      _ = ∏ r, cw2376DominanceGradeWeight r ^
            (∑ sigma ∈ cw2376TargetJointTypes,
              if sigma i = r then
                cw2376ProfileMultiplicity m sigma else 0) := by
        apply Finset.prod_congr rfl
        intro r hr
        exact congrArg (fun n => cw2376DominanceGradeWeight r ^ n)
          (ha i r)
      _ = ∏ sigma ∈ cw2376TargetJointTypes,
          cw2376DominanceGradeWeight (sigma i) ^
            cw2376ProfileMultiplicity m sigma :=
        (prod_pow_by_fiber_finset cw2376TargetJointTypes
          (fun sigma => sigma i) cw2376DominanceGradeWeight
          (cw2376ProfileMultiplicity m)).symm
  have hinner :
      (∏ sigma ∈ cw2376TargetJointTypes, (∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^ a sigma) =
        ∏ sigma ∈ cw2376TargetJointTypes, (∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^
            cw2376ProfileMultiplicity m sigma := by
    calc
      (∏ sigma ∈ cw2376TargetJointTypes, (∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^ a sigma) =
          ∏ i : Fin 3, ∏ sigma ∈ cw2376TargetJointTypes,
            cw2376DominanceGradeWeight (sigma i) ^ a sigma :=
        prod_prod_pow_swap_finset cw2376TargetJointTypes
          (fun sigma i => cw2376DominanceGradeWeight (sigma i)) a
      _ = ∏ i : Fin 3, ∏ sigma ∈ cw2376TargetJointTypes,
            cw2376DominanceGradeWeight (sigma i) ^
              cw2376ProfileMultiplicity m sigma := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hmode i
      _ = ∏ sigma ∈ cw2376TargetJointTypes, (∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^
            cw2376ProfileMultiplicity m sigma :=
        (prod_prod_pow_swap_finset cw2376TargetJointTypes
          (fun sigma i => cw2376DominanceGradeWeight (sigma i))
          (cw2376ProfileMultiplicity m)).symm
  have hweight :
      (∏ sigma ∈ cw2376TargetJointTypes, (m * ∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^ a sigma) =
        ∏ sigma ∈ cw2376TargetJointTypes, (m * ∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^
            cw2376ProfileMultiplicity m sigma := by
    calc
      (∏ sigma ∈ cw2376TargetJointTypes, (m * ∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^ a sigma) =
          m ^ (∑ sigma ∈ cw2376TargetJointTypes, a sigma) *
            ∏ sigma ∈ cw2376TargetJointTypes, (∏ i : Fin 3,
              cw2376DominanceGradeWeight (sigma i)) ^ a sigma :=
        prod_mul_pow_split_finset cw2376TargetJointTypes m _ a
      _ = m ^ (∑ sigma ∈ cw2376TargetJointTypes,
              cw2376ProfileMultiplicity m sigma) *
            ∏ sigma ∈ cw2376TargetJointTypes, (∏ i : Fin 3,
              cw2376DominanceGradeWeight (sigma i)) ^
                cw2376ProfileMultiplicity m sigma := by
        rw [htotal, hinner]
      _ = ∏ sigma ∈ cw2376TargetJointTypes, (m * ∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^
            cw2376ProfileMultiplicity m sigma :=
        (prod_mul_pow_split_finset cw2376TargetJointTypes m _
          (cw2376ProfileMultiplicity m)).symm
  have hscaled :
      (∏ sigma ∈ cw2376TargetJointTypes,
          (cw2376DominanceScale *
            cw2376ProfileMultiplicity m sigma) ^ a sigma) =
        ∏ sigma ∈ cw2376TargetJointTypes,
          (cw2376DominanceScale *
            cw2376ProfileMultiplicity m sigma) ^
              cw2376ProfileMultiplicity m sigma := by
    calc
      (∏ sigma ∈ cw2376TargetJointTypes,
          (cw2376DominanceScale *
            cw2376ProfileMultiplicity m sigma) ^ a sigma) =
          ∏ sigma ∈ cw2376TargetJointTypes, (m * ∏ i : Fin 3,
            cw2376DominanceGradeWeight (sigma i)) ^ a sigma := by
        apply Finset.prod_congr rfl
        intro sigma hsigma
        exact congrArg (fun n => n ^ a sigma)
          (mme_CW_2376_target_product_weight_identity m sigma hsigma)
      _ = ∏ sigma ∈ cw2376TargetJointTypes, (m * ∏ i : Fin 3,
          cw2376DominanceGradeWeight (sigma i)) ^
            cw2376ProfileMultiplicity m sigma := hweight
      _ = ∏ sigma ∈ cw2376TargetJointTypes,
          (cw2376DominanceScale *
            cw2376ProfileMultiplicity m sigma) ^
              cw2376ProfileMultiplicity m sigma := by
        apply Finset.prod_congr rfl
        intro sigma hsigma
        exact congrArg
          (fun n => n ^ cw2376ProfileMultiplicity m sigma)
          (mme_CW_2376_target_product_weight_identity m sigma hsigma).symm
  have hpow :
      (∏ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma ^ a sigma) =
        ∏ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma ^
            cw2376ProfileMultiplicity m sigma := by
    rw [prod_mul_pow_split_finset, prod_mul_pow_split_finset,
      htotal] at hscaled
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pow_pos (by norm_num [cw2376DominanceScale])) hscaled
  have hcoordinate :
      (∏ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma ^ a sigma *
            (cw2376ProfileMultiplicity m sigma).factorial) ≤
        ∏ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma ^
              cw2376ProfileMultiplicity m sigma *
            (a sigma).factorial := by
    exact Finset.prod_le_prod' fun sigma hsigma =>
      nat_pow_mul_factorial_mode
        (cw2376ProfileMultiplicity m sigma) (a sigma)
  have hcombined :
      (∏ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma ^ a sigma) *
          (∏ sigma ∈ cw2376TargetJointTypes,
            (cw2376ProfileMultiplicity m sigma).factorial) ≤
        (∏ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma ^
            cw2376ProfileMultiplicity m sigma) *
          (∏ sigma ∈ cw2376TargetJointTypes,
            (a sigma).factorial) := by
    simpa only [Finset.prod_mul_distrib] using hcoordinate
  rw [hpow] at hcombined
  have hpositive :
      0 < ∏ sigma ∈ cw2376TargetJointTypes,
        cw2376ProfileMultiplicity m sigma ^
          cw2376ProfileMultiplicity m sigma := by
    exact Finset.prod_pos fun sigma hsigma => Nat.pow_pos (hw sigma hsigma)
  have hfinal := Nat.le_of_mul_le_mul_left hcombined
  exact hfinal hpositive
