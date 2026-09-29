-- Prove2me | solution 1 for Teichmuller.LinMap.inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T08:10:01.442915+00:00
-- url     : https://prove2.me/submissions/f35fef8a-4238-4e43-8c4a-a954b5ee4cab

import Definitions.Def_Geometry_Teichmuller_LinearQC
open Teichmuller Complex in
theorem solution (f : LinMap) (z : ℂ) : f.toFun (f.inv.toFun z) = z := by
  have hJ0 : ((f.jac : ℝ) : ℂ) ≠ 0 := by exact_mod_cast f.jac_pos.ne'
  have hJ : ((f.jac : ℝ) : ℂ) = f.a * (starRingEnd ℂ) f.a - f.b * (starRingEnd ℂ) f.b := by
    rw [Complex.mul_conj', Complex.mul_conj']; simp [LinMap.jac]
  simp only [LinMap.toFun, LinMap.inv, map_add, map_mul, map_div₀, map_neg, Complex.conj_conj,
    Complex.conj_ofReal]
  field_simp
  linear_combination (-z) * hJ
