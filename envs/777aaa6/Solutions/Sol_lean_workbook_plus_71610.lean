-- Prove2me | solution 1 for lean_workbook_plus_71610
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:05:06.019256+00:00
-- url     : https://prove2.me/submissions/3049c72a-fe7c-45dd-bd9e-b63453ca4851

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem no_solution (f : ℤ → ℤ) (hf : ∀ x y, f y - f (y + f x) = x) : False := by
  have hcomp (x : ℤ) : f (f x) = f 0 - x := by
    have h := hf x 0
    simp only [zero_add] at h
    linarith
  have hinj : Function.Injective f := by
    intro x y h
    have h' := congrArg f h
    rw [hcomp, hcomp] at h'
    linarith
  have hzero : f 0 = 0 := by
    apply hinj
    simpa only [sub_zero] using hcomp 0
  have hcomp' (x : ℤ) : f (f x) = -x := by rw [hcomp, hzero, zero_sub]
  have hadd (x y : ℤ) : f (x + y) = f x + f y := by
    have h := hf (f y) (x + y)
    rw [hcomp', show x + y + -y = x by abel] at h
    linarith
  let F : ℤ →+ ℤ := {
    toFun := f
    map_zero' := hzero
    map_add' := hadd
  }
  have hlinear (n : ℤ) : f n = n * f 1 := by
    simpa only [zsmul_eq_mul, mul_one] using map_zsmul F n (1 : ℤ)
  have hbad := hcomp' 1
  rw [hlinear (f 1)] at hbad
  nlinarith [sq_nonneg (f 1)]

theorem solution (f : ℤ → ℤ) (hf : ∀ x y, f y - f (y + f x) = x) :
    ∃ a, ∀ x, f x = a - x := False.elim (no_solution f hf)

theorem full_classification : ¬ ∃ f : ℤ → ℤ, ∀ x y, f y - f (y + f x) = x := by
  rintro ⟨f, hf⟩
  exact no_solution f hf

#print axioms solution
#print axioms no_solution
#print axioms full_classification
