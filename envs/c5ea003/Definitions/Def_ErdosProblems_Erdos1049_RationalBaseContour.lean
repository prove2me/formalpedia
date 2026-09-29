-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
-- name    : ErdosProblems_Erdos1049_RationalBaseContour
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:45:24.900326+00:00
-- url     : https://prove2.me/theorems/754e0adc-288a-4279-87c6-9dde7de2ac8c
-- title:
--   Erdős #1049: the rational-base contour of Zudilin's `(14,12,14;27)` forms
-- statement:
--   The rational-base contour compares denominator and remainder rates of Zudilin's (14,12,14;27) forms after homogeneous evaluation. The submitted module contains the source declarations trigammaSeries, summable_trigammaTerm, trigammaSeries_nonneg, trigammaSeries_antitone, sum_le_trigammaSeries_sub, among others. Source topic: Erdős #1049: the rational-base contour of Zudilin's `(14,12,14;27)` forms.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/RationalBaseContour.lean#L46-L355
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
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

/-- The series representation of the trigamma function.  Only this series is
used; the identification with `d²/dx² log Γ` is classical and not needed. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2













/-! ## The thirteen intervals and the constant `J` -/

/-- One interval's contribution `ψ₁(u) - ψ₁(v)`. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v

/-- `J = ∫₀¹ ω(x) d(-ψ'(x))` over the thirteen intervals on which `ω = 1`
(Zudilin 2004, end of Section 5), written as the trigamma series. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)

/-- `C₁ = (α₀+α₁+α₂)β - (α₁²+α₂²+β²)/2 = 1091/2`, Zudilin's (25). -/
noncomputable def zudilinC1 : ℝ := 1091 / 2

/-- `C₀ = α₁²/2 + α₀α₁ + (β-α₂)(α₂-α₁) - (3/π²)(m² - J)` with `m = 15`,
Zudilin's (26). -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)

/-- The rational-base threshold `θ* = C₀/C₁ = 1/μ`, where `μ = C₁/C₀` is the
irrationality-exponent bound of Zudilin's Theorem 1. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

/-- The parameter region of the authored rational-base theorem: reduced bases
`a/b` with `log b / log a < θ*`.  Membership is the hypothesis the ordinary
proof consumes; it is not an irrationality statement. -/
def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

/-! ## Lower bound: `J > 77.6`, hence `θ* > 81/200` -/











/-! ## Upper bound: `J < ψ₁(1/14) < 198`, hence `θ* < 1/2` -/











/-! ## Membership and exclusion -/













/-! ## Exact integer bookkeeping of the forms at index `n` -/
















end ErdosProblems.Erdos1049


