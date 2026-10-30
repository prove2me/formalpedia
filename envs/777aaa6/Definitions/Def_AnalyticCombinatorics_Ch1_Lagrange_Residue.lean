-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_Residue
-- name    : AnalyticCombinatorics_Ch1_Lagrange_Residue
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:02:06.742987+00:00
-- url     : https://prove2.me/theorems/5038e5b3-8a78-401f-a72f-0e401f534dd3
-- title:
--   Formal coefficient residues and unit-series kernels
-- statement:
--   Over a commutative ring $R$, for $F\in R[[X]]$ and $N\in\mathbb{N}$, define the shifted coefficient $\operatorname{resShift}(N,F)=[X^{N-1}]F$ and the derivative numerator $XF'-N_RF$, where $N_R=N\cdot1_R$. Subtraction in the index is natural subtraction, so $N=0$ and $N=1$ both select the constant coefficient. For a unit $U$ of $R[[X]]$, write $u$ for its underlying series and $v$ for the series underlying $U^{-1}$. Define $\operatorname{unitKernel}(U,m)=v^m(u+Xu')$. This encodes coefficient operations on formal power series; it does not introduce a Laurent-series carrier or an analytic contour integral.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Lagrange/Residue.lean
--   Source code license: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Formal residues for the Lagrange inversion proof

This file uses the lightweight Laurent representation `X^{-N} * F`, with
`F : R⟦X⟧`.  The residue is the coefficient of `X^{N-1}` in `F`.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch1.Lagrange.Residue

open PowerSeries

variable {R : Type*} [CommRing R]

/-- Residue of the lightweight Laurent series represented by `X^{-N} * F`. -/
def resShift (N : ℕ) (F : R⟦X⟧) : R :=
  coeff (N - 1) F

/-- Numerator of the derivative of `X^{-N} * F`, represented with denominator `X^{N+1}`. -/
def shiftDerivNumer (N : ℕ) (F : R⟦X⟧) : R⟦X⟧ :=
  X * d⁄dX R F - C (N : R) * F

def unitSeries (U : R⟦X⟧ˣ) : R⟦X⟧ :=
  (U : R⟦X⟧)

def unitInvSeries (U : R⟦X⟧ˣ) : R⟦X⟧ :=
  (U⁻¹ : R⟦X⟧ˣ)

/-- The power-series numerator of `(X * U)^{-m} * (X * U)'`. -/
def unitKernel (U : R⟦X⟧ˣ) (m : ℕ) : R⟦X⟧ :=
  (unitInvSeries U ^ m) * (unitSeries U + X * d⁄dX R (unitSeries U))

end AnalyticCombinatorics.Ch1.Lagrange.Residue


