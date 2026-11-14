-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:14.144646+00:00
-- url     : https://prove2.me/theorems/22311f24-36b1-4ed6-a7c9-10bb4191ee6c
-- title:
--   Smooth sieve cutoffs and derivative energy
-- statement:
--   A smooth sieve cutoff is a function $\chi:\mathbb R\to\mathbb R$ that is infinitely differentiable, takes values in $[0,1]$, is supported in $[-1,1]$, satisfies $\chi(0)=1$, and vanishes for $x\ge1$. The associated derivative-energy normalizer is
--
--   $$
--   c_\chi=\int_{(0,\infty)}|\chi'(x)|^2\,dx.
--   $$
--
--   The cutoff is also supplied as a callable function. A concrete example is constructed from a smooth bump with inner radius $1/2$ and outer radius $1$. These objects provide the cutoff and normalization used in the Goldston–Yıldırım divisor sum and the Selberg majorant.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/SmoothCutoff.lean#L22-L158

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Lean

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/

namespace Wikipedia.SzemeredisTheorem

open Function Set MeasureTheory
open scoped ContDiff

/-- A smooth real cutoff taking values in `[0, 1]`, equal to one at zero,
and supported in `[-1, 1]`. -/
structure SmoothSieveCutoff where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  support_subset : Function.support toFun ⊆ Set.Icc (-1) 1
  zero_of_one_le : ∀ x, 1 ≤ x → toFun x = 0
  value_zero : toFun 0 = 1

namespace SmoothSieveCutoff

instance : CoeFun SmoothSieveCutoff fun _ ↦ ℝ → ℝ :=
  ⟨SmoothSieveCutoff.toFun⟩









/-- The derivative-square energy normalizing the Selberg majorant. -/
noncomputable def normalizer (χ : SmoothSieveCutoff) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), |deriv χ.toFun x| ^ 2









end SmoothSieveCutoff

/-- A concrete bump with inner radius `1/2` and outer radius `1`. -/
noncomputable def standardSmoothSieveBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The standard smooth sieve cutoff obtained from Mathlib's bump
function on `ℝ`. -/
noncomputable def standardSmoothSieveCutoff : SmoothSieveCutoff where
  toFun := standardSmoothSieveBump
  smooth := ContDiffBump.contDiff standardSmoothSieveBump
  nonneg := fun x ↦ ContDiffBump.nonneg' standardSmoothSieveBump x
  le_one := fun _ ↦ ContDiffBump.le_one standardSmoothSieveBump
  support_subset := by
    rw [ContDiffBump.support_eq]
    intro x hx
    have habs : |x| < 1 := by
      simpa [standardSmoothSieveBump, Metric.mem_ball, Real.dist_eq] using hx
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  zero_of_one_le := by
    intro x hx
    apply ContDiffBump.zero_of_le_dist standardSmoothSieveBump
    change (1 : ℝ) ≤ dist x 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (zero_le_one.trans hx)]
    exact hx
  value_zero := by
    apply ContDiffBump.one_of_mem_closedBall standardSmoothSieveBump
    simp [standardSmoothSieveBump]







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `ContDiffBump.mk.congr_simp,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.ctorIdx,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.mk.inj,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.mk.injEq,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.noConfusionType,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.normalizer.eq_1,
    `Wikipedia.SzemeredisTheorem.standardSmoothSieveBump.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


