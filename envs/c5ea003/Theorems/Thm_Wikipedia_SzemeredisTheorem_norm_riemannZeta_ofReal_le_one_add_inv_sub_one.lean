-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_riemannZeta_ofReal_le_one_add_inv_sub_one
-- name    : Wikipedia.SzemeredisTheorem.norm_riemannZeta_ofReal_le_one_add_inv_sub_one
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:20:28.410815+00:00
-- url     : https://prove2.me/theorems/63ddae23-1201-4474-a529-6e7931049344
-- title:
--   An elementary upper bound for zeta on the real axis
-- statement:
--   For every real $s>1$, the Riemann zeta function satisfies
--
--   $$
--   |\zeta(s)|\le1+\frac1{s-1}.
--   $$
--
--   The zeta value is regarded as complex and its usual complex norm is used.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/PrimeHarmonicProductBound.lean#L39-L115

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Polylogarithmic bounds for a finite prime Euler product

This file bounds

`∏ p ∈ Nat.primesLE R, (1 + A / p)`.

The elementary comparison with the full harmonic sum gives an exponential
bound.  More importantly for Fourier-tail estimates, shifting the Euler
product of the Riemann zeta function to

`s = 1 + 1 / log R`

gives a polynomial bound in `log R`.  This avoids requiring a separately
formalized Mertens theorem.
-/
open Wikipedia.SzemeredisTheorem
open Filter Set
open scoped BigOperators Topology

theorem Wikipedia.SzemeredisTheorem.norm_riemannZeta_ofReal_le_one_add_inv_sub_one
    {s : ℝ} (hs : 1 < s) :
    ‖riemannZeta (s : ℂ)‖ ≤ 1 + (s - 1)⁻¹ := by sorry
