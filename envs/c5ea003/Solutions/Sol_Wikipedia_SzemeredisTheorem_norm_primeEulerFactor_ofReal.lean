-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_primeEulerFactor_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:55.729591+00:00
-- url     : https://prove2.me/submissions/581b5cff-ec2b-45b4-b7e2-cd0d157c42e0

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

open Wikipedia.SzemeredisTheorem in
/-- A real Euler factor is also the norm of the corresponding complex
Euler factor. -/
theorem solution
    {p : ℕ} (hp : 2 ≤ p) {s : ℝ} (hs : 0 < s) :
    ‖(1 - (p : ℂ) ^ (-((s : ℝ) : ℂ)))⁻¹‖ =
      (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have hpR : (0 : ℝ) ≤ p := by positivity
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp
  have hxlt : (p : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl ⟨hpOne, by linarith⟩)
  have hpos : 0 < 1 - (p : ℝ) ^ (-s) := sub_pos.mpr hxlt
  have hcast :
      (1 - (p : ℂ) ^ (-((s : ℝ) : ℂ)))⁻¹ =
        (((1 - (p : ℝ) ^ (-s))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_cpow hpR]
    simp
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
