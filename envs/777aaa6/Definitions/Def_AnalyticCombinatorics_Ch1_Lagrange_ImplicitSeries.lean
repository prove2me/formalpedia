-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_ImplicitSeries
-- name    : AnalyticCombinatorics_Ch1_Lagrange_ImplicitSeries
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:01:20.035163+00:00
-- url     : https://prove2.me/theorems/cf5739f0-85e6-498d-a27c-d92331d3d3d9
-- title:
--   Implicit formal power series by coefficient recursion
-- statement:
--   Over a commutative ring $R$, let $P_n(a)=\sum_{k<n}a_kX^k$. The coefficient recursion starts with $a_0=0$ and sets $a_{m+1}=[X^m]\varphi(P_{m+1}(a))$ for an arbitrary formal series $\varphi\in R[[X]]$. The resulting series is $T_\varphi=\sum_{j\geq0}a_jX^j$. The intermediate step operation also accepts an arbitrary supplied family of earlier coefficients and applies formal substitution; it does not assume that an arbitrary such family has zero constant coefficient. The definitions additionally include the series $X\sum_{j\geq0}X^j$. These are formal constructions, without analytic convergence assumptions. The coefficient identities are stated separately for the constructed recursive series.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Lagrange/ImplicitSeries.lean
--   Source code license: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Implicit formal power series

This file constructs, coefficient by coefficient, the unique formal power
series `T` with zero constant term satisfying `T = X * φ.subst T`.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch1.Lagrange

open PowerSeries

variable {R : Type*} [CommRing R]

namespace ImplicitSeries

def partialSeries (a : ℕ → R) (n : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun k => if k < n then a k else 0

def implicitStep (φ : R⟦X⟧) (n : ℕ) (rec : ∀ k, k < n → R) : R :=
  match n with
  | 0 => 0
  | m + 1 =>
      coeff m (φ.subst (partialSeries (fun k => if h : k < m + 1 then rec k h else 0) (m + 1)))

def implicitCoeff (φ : R⟦X⟧) : ℕ → R :=
  Nat.strongRec (implicitStep φ)

def implicitSeries (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (implicitCoeff φ)

section Sanity

def geometricTail : R⟦X⟧ :=
  X * (PowerSeries.mk fun _ => (1 : R))

end Sanity

end ImplicitSeries

end AnalyticCombinatorics.Ch1.Lagrange


