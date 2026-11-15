-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.ConvolutionMixture.eval_mul
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:12.637345+00:00
-- url     : https://prove2.me/submissions/2d717e2d-0cdf-4663-b2ff-0d4d019b9a4e

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_generalizedConvolution_mul_eq_mean

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
/-! ## Finite convex mixtures -/
open Wikipedia.SzemeredisTheorem.ConvolutionMixture

open Wikipedia.SzemeredisTheorem.ConvolutionMixture in
/-- Evaluation of the product mixture is pointwise multiplication. -/
theorem solution
    {G : Type u} [Fintype G] [AddCommGroup G] (n : ℕ)
    (m₁ m₂ : ConvolutionMixture G (n + 1)) (z : G) :
    (mul n m₁ m₂).eval z = m₁.eval z * m₂.eval z := by
  let : Fintype m₁.ι := m₁.indexFintype
  let : Fintype m₂.ι := m₂.indexFintype
  let : Nonempty m₁.ι := m₁.indexNonempty
  let : Nonempty m₂.ι := m₂.indexNonempty
  change
    mean (fun p : m₁.ι × (m₂.ι × (Fin n → G)) =>
      generalizedConvolution (n + 1)
        (convolutionProductCutTest n
          (m₁.tests p.1) (m₂.tests p.2.1) p.2.2) z) =
      mean (fun a : m₁.ι =>
        generalizedConvolution (n + 1) (m₁.tests a) z) *
      mean (fun b : m₂.ι =>
        generalizedConvolution (n + 1) (m₂.tests b) z)
  calc
    mean (fun p : m₁.ι × (m₂.ι × (Fin n → G)) =>
        generalizedConvolution (n + 1)
          (convolutionProductCutTest n
            (m₁.tests p.1) (m₂.tests p.2.1) p.2.2) z) =
        mean₂ (fun a : m₁.ι =>
          fun p : m₂.ι × (Fin n → G) =>
            generalizedConvolution (n + 1)
              (convolutionProductCutTest n
                (m₁.tests a) (m₂.tests p.1) p.2) z) :=
      by
        simpa [mean, mean₂] using
          (Finset.expect_product'
            (Finset.univ : Finset m₁.ι)
            (Finset.univ :
              Finset (m₂.ι × (Fin n → G)))
            (fun a : m₁.ι =>
              fun p : m₂.ι × (Fin n → G) =>
                generalizedConvolution (n + 1)
                  (convolutionProductCutTest n
                    (m₁.tests a) (m₂.tests p.1) p.2) z))
    _ = mean (fun a : m₁.ι =>
          mean₂ (fun b : m₂.ι => fun d : Fin n → G =>
            generalizedConvolution (n + 1)
              (convolutionProductCutTest n
                (m₁.tests a) (m₂.tests b) d) z)) := by
      unfold mean₂
      apply congrArg mean
      funext a
      simpa [mean, mean₂] using
        (Finset.expect_product'
          (Finset.univ : Finset m₂.ι)
          (Finset.univ : Finset (Fin n → G))
          (fun b : m₂.ι => fun d : Fin n → G =>
            generalizedConvolution (n + 1)
              (convolutionProductCutTest n
                (m₁.tests a) (m₂.tests b) d) z))
    _ = mean₂ (fun a : m₁.ι => fun b : m₂.ι =>
          generalizedConvolution (n + 1) (m₁.tests a) z *
            generalizedConvolution (n + 1) (m₂.tests b) z) := by
      unfold mean₂
      apply congrArg mean
      funext a
      apply congrArg mean
      funext b
      exact
        (generalizedConvolution_mul_eq_mean
          n (m₁.tests a) (m₂.tests b) z).symm
    _ = mean (fun a : m₁.ι =>
          generalizedConvolution (n + 1) (m₁.tests a) z) *
        mean (fun b : m₂.ι =>
          generalizedConvolution (n + 1) (m₂.tests b) z) := by
      simpa [mean, mean₂] using
        (Fintype.expect_mul_expect
          (fun a : m₁.ι =>
            generalizedConvolution (n + 1) (m₁.tests a) z)
          (fun b : m₂.ι =>
            generalizedConvolution (n + 1) (m₂.tests b) z)).symm
