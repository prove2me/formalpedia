-- Prove2me | Theorems.Thm_logDeriv_intervalIntegral_eq_of_homotopy
-- name    : logDeriv_intervalIntegral_eq_of_homotopy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T19:02:19.779836+00:00
-- url     : https://prove2.me/theorems/d56114a2-415c-4d8d-a4a3-7b0018dfe5f7
-- title:
--   Homotopy invariance of the winding integral $\int_0^1 F'/F$
-- statement:
--   Let $F:[0,1]\times\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be continuous, differentiable in $s$ with $\partial_sF$ continuous on $[0,1]\times\mathbb{R}$, and closed in $s$: $F(r,1)=F(r,0)$. Then the winding integral does not depend on $r$:
--   $$\int_0^1\frac{\partial_sF(1,s)}{F(1,s)}\,ds=\int_0^1\frac{\partial_sF(0,s)}{F(0,s)}\,ds.$$
--   Each integral lies in $2\pi i\mathbb{Z}$ because $F(r,s)=F(r,0)\exp\int_0^s\partial_sF/F$. It is continuous in $r$, hence constant.
-- source:
--   Standard winding-number calculus for C^1 loops in C \ {0}; used for the conormal winding of a disk-like global surface of section in Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 1.7 (via Hryniewicz, Trans. AMS 364 (2012), Prop. 2.1).

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

open scoped ContDiff

theorem logDeriv_intervalIntegral_eq_of_homotopy {F F' : ℝ → ℝ → ℂ}
    (hF : ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ s, HasDerivAt (F r) (F' r s) s)
    (hcF : ContinuousOn (Function.uncurry F) (Set.Icc 0 1 ×ˢ Set.univ))
    (hcF' : ContinuousOn (Function.uncurry F') (Set.Icc 0 1 ×ˢ Set.univ))
    (hne : ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ s, F r s ≠ 0)
    (hper : ∀ r ∈ Set.Icc (0 : ℝ) 1, F r 1 = F r 0) :
    ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by sorry
