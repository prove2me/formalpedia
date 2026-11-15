-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_primeEulerFactor_ofReal
-- name    : Wikipedia.SzemeredisTheorem.norm_primeEulerFactor_ofReal
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:27:55.677925+00:00
-- url     : https://prove2.me/theorems/7ce78d6c-d364-4642-8204-0242c7fcccef
-- title:
--   The norm of an Euler factor at a positive real exponent
-- statement:
--   For a natural base $p\ge2$ and a real exponent $s>0$,
--
--   $$
--   \left|(1-p^{-s})^{-1}\right|=(1-p^{-s})^{-1},
--   $$
--
--   with the expression on the left interpreted in $\mathbb C$ and the one on the right in $\mathbb R$. The complex power agrees with the real power at this positive base. Primality of $p$ is not assumed.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/PrimeHarmonicProductBound.lean#L117-L136

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

theorem Wikipedia.SzemeredisTheorem.norm_primeEulerFactor_ofReal
    {p : ℕ} (hp : 2 ≤ p) {s : ℝ} (hs : 0 < s) :
    ‖(1 - (p : ℂ) ^ (-((s : ℝ) : ℂ)))⁻¹‖ =
      (1 - (p : ℝ) ^ (-s))⁻¹ := by sorry
