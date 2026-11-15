-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaSystemFactor_eq_prod
-- name    : Wikipedia.SzemeredisTheorem.cutoffZetaSystemFactor_eq_prod
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:38.998739+00:00
-- url     : https://prove2.me/theorems/0df2b9c4-aad3-4b4a-971b-bf731fafc10a
-- title:
--   Expanding the completed cutoff zeta-system factor
-- statement:
--   For a natural $R>1$ and two real frequency families on a finite type $K$, put $z_q=(1-2\pi it_q)/\log R$ and $v_q=(1-2\pi iu_q)/\log R$. The completed system factor equals
--
--   $$
--   Z_{\rm comp}(R,t,u)=\prod_{q\in K}
--   \frac{z_q+v_q}{z_qv_q}
--   \frac{\zeta(1+z_q+v_q)}{\zeta(1+z_q)\zeta(1+v_q)}.
--   $$
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L203-L232

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## Finite Fourier systems -/

theorem Wikipedia.SzemeredisTheorem.cutoffZetaSystemFactor_eq_prod
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSystemFactor R t u =
      ∏ i,
        (((cutoffZetaShift R (t i) +
              cutoffZetaShift R (u i)) /
            (cutoffZetaShift R (t i) *
              cutoffZetaShift R (u i))) *
          (riemannZeta
                (1 + cutoffZetaShift R (t i) +
                  cutoffZetaShift R (u i)) /
            (riemannZeta
                  (1 + cutoffZetaShift R (t i)) *
              riemannZeta
                  (1 + cutoffZetaShift R (u i))))) := by sorry
