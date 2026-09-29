-- Prove2me | solution 1 for ErdosProblems.Erdos1049.zudilinC1_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:12:55.830043+00:00
-- url     : https://prove2.me/submissions/134136b3-0c82-4075-a978-07e7cba966a2

import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Erdős #1049: the rational-base contour of Zudilin's `(14,12,14;27)` forms

The proof note `RationalBaseIrrationality_31_4_Proof.md` shows that the linear
forms of W. Zudilin, *Heine's basic transform and a permutation group for
q-harmonic series*, Acta Arith. 111 (2004) 153–164, in the direction
`(α₀,α₁,α₂;β) = (14,12,14;27)`, after homogenisation at a reduced rational base
`a/b`, prove that `F(a/b) = ∑_{m≥1} 1/((a/b)^m - 1)` is irrational whenever

`log b / log a < θ* := C₀ / C₁`,   `C₁ = 1091/2`,   `C₀ = 266 - (3/π²)(225 - J)`,

where `J = ∑_{i=1}^{13} (ψ₁(uᵢ) - ψ₁(vᵢ))` is the trigamma integral of Zudilin's
step function `ω` over its thirteen printed intervals `[uᵢ, vᵢ)` and
`ψ₁(x) = ∑_{k≥0} 1/(k+x)²`.

This module formalises the finite part of that theorem: the constants are
defined from the trigamma series, and Lean proves

* `eightyOne_twoHundredths_lt_zudilinContour : 81/200 < θ*` from the single
  `k = 0` term of each trigamma difference and `π > 3.14`;
* `zudilinContour_lt_half : θ* < 1/2` from `J < ψ₁(1/14) < 198`;
* membership of `31/4` and every power `(31/4)^r` in the contour region, and
  the inclusion of the older `81/200` region in it;
* exclusion of `3/2` from the contour region;
* the exact integer bookkeeping of the forms: `2M(a;b) = 2(266n² + 34n + 1)`,
  the degree step `d_{k+1} - d_k = 40n + 1 - k`, and the top degree
  `2 d_{b-1} = 1091n² + 81n + 2`.

No analytic step is formalised.  Zudilin's Lemma 7 (integrality in `ℤ[p]`),
his Lemma 2 (trigamma equidistribution of `φ(l)`), and the Archimedean
estimate stay in the ordinary proof note.  Membership in the contour region is
the exact hypothesis that note consumes; it is not by itself an irrationality
statement.
-/

namespace ErdosProblems.Erdos1049
/-! ## The trigamma series `ψ₁(x) = ∑_{k≥0} 1/(k+x)²` -/















/-! ## The thirteen intervals and the constant `J` -/













/-! ## Lower bound: `J > 77.6`, hence `θ* > 81/200` -/
end ErdosProblems.Erdos1049

open ErdosProblems in
open ErdosProblems.Erdos1049 in
theorem solution : 0 < zudilinC1 := by unfold zudilinC1; norm_num
