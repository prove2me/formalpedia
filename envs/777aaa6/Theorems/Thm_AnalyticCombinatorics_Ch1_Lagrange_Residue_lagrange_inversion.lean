-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_Lagrange_Residue_lagrange_inversion
-- name    : AnalyticCombinatorics.Ch1.Lagrange.Residue.lagrange_inversion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:03:07.151981+00:00
-- url     : https://prove2.me/theorems/e1922e7f-322c-49af-87e8-2983392a5aac
-- title:
--   Formal Lagrange inversion with the integer factor retained
-- statement:
--   Let $R$ be a commutative ring equipped with a specified $\mathbb{Q}$-algebra structure, and let $\varphi(X)\in R[[X]]$ have an invertible constant coefficient. Let $T(X)$ be the recursively constructed formal series of the source, with zero constant coefficient and satisfying
--
--   $$T(X)=X\varphi(T(X)).$$
--
--   For every natural number $n>0$,
--
--   $$(n\cdot1_R)[X^n]T(X)=[X^{n-1}]\varphi(X)^n.$$
--
--   Here $[X^j]$ denotes the coefficient at degree $j$. This gives coefficients of the implicit series in terms of powers of its defining series, with the integer scalar retained. It is an identity of formal power series coefficients and requires no analytic convergence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Lagrange/Residue.lean#L286
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

theorem AnalyticCombinatorics.Ch1.Lagrange.Residue.lagrange_inversion [Algebra ℚ R] (φ : R⟦X⟧)
    (hφ : IsUnit (constantCoeff φ)) (n : ℕ) (hn : 0 < n) :
    (n : R) * coeff n (ImplicitSeries.implicitSeries φ) =
      coeff (n - 1) (φ ^ n) := by sorry
