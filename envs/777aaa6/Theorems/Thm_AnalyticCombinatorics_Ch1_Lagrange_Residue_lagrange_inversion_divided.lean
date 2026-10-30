-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_Lagrange_Residue_lagrange_inversion_divided
-- name    : AnalyticCombinatorics.Ch1.Lagrange.Residue.lagrange_inversion_divided
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:02:44.633831+00:00
-- url     : https://prove2.me/theorems/b6dbfc71-09de-480a-aa19-b8f163c4714e
-- title:
--   Formal Lagrange inversion using the rational scalar inverse
-- statement:
--   Let $R$ be a commutative ring with specified $\mathbb{Q}$-algebra structure map $\iota:\mathbb{Q}\to R$. Let $\varphi(X)\in R[[X]]$ have invertible constant coefficient, and let $T$ be the source's recursively constructed zero-constant formal solution of $T=X\varphi(T)$. For every natural number $n>0$,
--
--   $$[X^n]T(X)=\iota(1/n)[X^{n-1}]\varphi(X)^n.$$
--
--   The inverse $1/n$ is formed in $\mathbb{Q}$ and transported to $R$ by $\iota$; division on $R$ is not assumed. This is the usual coefficient-extraction form for the implicit-series construction, over the same ring and unit-constant hypotheses as the factor-retained identity.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Lagrange/Residue.lean#L335
--   Source code license: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_ImplicitSeries
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Formal residues for the Lagrange inversion proof

This file uses the lightweight Laurent representation `X^{-N} * F`, with
`F : R⟦X⟧`.  The residue is the coefficient of `X^{N-1}` in `F`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1 AnalyticCombinatorics.Ch1.Lagrange

open PowerSeries

variable {R : Type*} [CommRing R]

theorem AnalyticCombinatorics.Ch1.Lagrange.Residue.lagrange_inversion_divided [Algebra ℚ R] (φ : R⟦X⟧)
    (hφ : IsUnit (constantCoeff φ)) (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries φ) =
      algebraMap ℚ R ((n : ℚ)⁻¹) * coeff (n - 1) (φ ^ n) := by sorry
