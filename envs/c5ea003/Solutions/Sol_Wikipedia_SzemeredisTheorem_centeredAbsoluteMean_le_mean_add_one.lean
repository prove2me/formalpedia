-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.centeredAbsoluteMean_le_mean_add_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:07:40.682892+00:00
-- url     : https://prove2.me/submissions/b9f26ceb-6a32-496b-a76f-3796f78853e6

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
/-- For a nonnegative majorant, its centered absolute mean is bounded by
its mean plus one. -/
theorem solution
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} (hν : ∀ x, 0 ≤ ν x) :
    centeredAbsoluteMean ν ≤ mean ν + 1 := by
  unfold centeredAbsoluteMean
  calc
    mean (fun x => |ν x - 1|) ≤
        mean (fun x => ν x + 1) := by
      apply mean_mono
      intro x
      rw [abs_le]
      constructor <;> linarith [hν x]
    _ = mean ν + mean (fun _ : Ω => (1 : ℝ)) :=
      mean_add _ _
    _ = mean ν + 1 := by
      rw [mean_const]
