-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_finitePairing_le_mul_mean_abs
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:05:01.532787+00:00
-- url     : https://prove2.me/submissions/61a16d05-e5cc-4083-844a-d4f35353e50c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite products and polynomial expansions -/
/-! ## Bounded combinations and approximation of positive part -/
/-! ## Quantitative positive-part correlation -/

open Wikipedia.SzemeredisTheorem in
/-- An error bounded pointwise by `δ` contributes at most `δ` times the
mean absolute size of the left factor to a normalized pairing. -/
theorem solution
    {Ω : Type*} [Fintype Ω]
    (f e : Ω → ℝ) {δ : ℝ}
    (he : ∀ x, |e x| ≤ δ) :
    |finitePairing f e| ≤ δ * mean (fun x => |f x|) := by
  calc
    |finitePairing f e| ≤ mean (fun x => |f x * e x|) := by
      unfold finitePairing mean
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun x => δ * |f x|) := by
      apply mean_mono
      intro x
      rw [abs_mul]
      have hmul :=
        mul_le_mul_of_nonneg_left (he x) (abs_nonneg (f x))
      simpa [mul_comm] using hmul
    _ = δ * mean (fun x => |f x|) :=
      mean_smul δ _
