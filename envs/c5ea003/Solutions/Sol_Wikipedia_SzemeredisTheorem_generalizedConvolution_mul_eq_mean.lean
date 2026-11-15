-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.generalizedConvolution_mul_eq_mean
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:28:17.684531+00:00
-- url     : https://prove2.me/submissions/ffbaae28-ce0c-4e6e-8be7-10df41f6ea70

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_mul_mean_eq_doubleMean_add

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

section


/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl



















@[simp]
theorem generalizedConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z =
      mean fun y : Fin n → G =>
        cutTestProduct u (sumFiberTuple n z y) :=
  rfl











































end Wikipedia.SzemeredisTheorem

end

section



/-!
# Multiplicative closure of generalized convolutions

The dense-model proof tests against generalized convolutions.  Products of
these tests remain convex averages of generalized convolutions: two points
in the same coordinate-sum fiber differ by a tuple of sum zero, and fixing
that difference turns the two cut products into one cut product.

This file proves the exact finite identity, packages finite convex mixtures,
and transfers a single cut-discrepancy estimate to every monomial required
by polynomial dense-model duality.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

universe u







/-- Add a fixed zero-sum displacement to a full fiber tuple. -/
theorem sumFiberTuple_add_zeroSumShift
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (z : G) (x d : Fin n → G) :
    (fun i : Fin (n + 1) =>
      sumFiberTuple n z x i + zeroSumShift n d i) =
        sumFiberTuple n z (fun t => x t + d t) := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  change
    (z - ∑ t, x t) + (0 - ∑ t, d t) =
      z - ∑ t, (x t + d t)
  rw [Finset.sum_add_distrib]
  abel





/-- Pointwise form of the fixed-displacement cut-product identity. -/
theorem cutTestProduct_convolutionProductCutTest
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1))
    (d : Fin n → G) (x : Fin (n + 1) → G) :
    cutTestProduct
        (convolutionProductCutTest n u v d) x =
      cutTestProduct u x *
        cutTestProduct v
          (fun i => x i + zeroSumShift n d i) := by
  rw [cutTestProduct, cutTestProduct, cutTestProduct]
  simp only [convolutionProductCutTest]
  rw [Finset.prod_mul_distrib]
  apply congrArg
  apply Finset.prod_congr rfl
  intro i _
  congr 1

/-- Tail-coordinate form of the same identity. -/
theorem cutTestProduct_convolutionProductCutTest_sumFiberTuple
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1))
    (z : G) (d x : Fin n → G) :
    cutTestProduct
        (convolutionProductCutTest n u v d)
        (sumFiberTuple n z x) =
      cutTestProduct u (sumFiberTuple n z x) *
        cutTestProduct v
          (sumFiberTuple n z (fun t => x t + d t)) := by
  rw [cutTestProduct_convolutionProductCutTest,
    sumFiberTuple_add_zeroSumShift]



/-! ## Finite convex mixtures -/



namespace ConvolutionMixture



















end ConvolutionMixture

/-! ## Consequences for dense-model moments -/











end Wikipedia.SzemeredisTheorem

end
/-!
# Multiplicative closure of generalized convolutions

The dense-model proof tests against generalized convolutions.  Products of
these tests remain convex averages of generalized convolutions: two points
in the same coordinate-sum fiber differ by a tuple of sum zero, and fixing
that difference turns the two cut products into one cut product.

This file proves the exact finite identity, packages finite convex mixtures,
and transfers a single cut-discrepancy estimate to every monomial required
by polynomial dense-model duality.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
universe u

open Wikipedia.SzemeredisTheorem in
/-- Exact multiplicative closure: a product of two generalized
convolutions is the normalized average of generalized convolutions indexed
by the zero-sum displacement between their fiber points. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z *
        generalizedConvolution (n + 1) v z =
      mean (fun d : Fin n → G =>
        generalizedConvolution (n + 1)
          (convolutionProductCutTest n u v d) z) := by
  rw [generalizedConvolution_succ,
    generalizedConvolution_succ,
    Wikipedia.SzemeredisTheorem.mean_mul_mean_eq_doubleMean_add]
  unfold mean₂
  apply congrArg mean
  funext d
  rw [generalizedConvolution_succ]
  apply congrArg mean
  funext x
  exact
    (cutTestProduct_convolutionProductCutTest_sumFiberTuple
      n u v z d x).symm
