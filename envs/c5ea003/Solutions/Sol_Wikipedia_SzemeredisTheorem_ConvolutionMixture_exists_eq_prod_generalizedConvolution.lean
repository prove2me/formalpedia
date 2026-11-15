-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.ConvolutionMixture.exists_eq_prod_generalizedConvolution
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:30.726129+00:00
-- url     : https://prove2.me/submissions/a31c2832-6e3d-4921-a675-e181e17e6d3a

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_ConvolutionMixture_eval_mul
import Theorems.Thm_Wikipedia_SzemeredisTheorem_generalizedConvolution_one_succ

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



















/-! ## Finite convex mixtures -/



namespace ConvolutionMixture





@[simp]
theorem eval_pure
    {G : Type u} [Fintype G] [AddCommGroup G] {r : ℕ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u)
    (z : G) :
    (pure u hu).eval z = generalizedConvolution r u z := by
  change
    mean (fun _ : ULift.{u} Unit => generalizedConvolution r u z) =
      generalizedConvolution r u z
  exact mean_const _



@[simp]
theorem eval_one
    {G : Type u} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    (one (G := G) n).eval z = 1 := by
  rw [one, eval_pure, generalizedConvolution_one_succ]









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
/-! ## Finite convex mixtures -/
open Wikipedia.SzemeredisTheorem.ConvolutionMixture

open Wikipedia.SzemeredisTheorem.ConvolutionMixture in
/-- Every finite product of bounded generalized convolutions is represented
by a finite convolution mixture. -/
theorem solution
    {G : Type u} [Fintype G] [AddCommGroup G] (r : ℕ) :
    ∀ (m : ℕ) (u : Fin m → CutTestFamily G (r + 1)),
      (∀ a, IsBoundedCutTest (u a)) →
      ∃ q : ConvolutionMixture G (r + 1),
        q.eval =
          fun z => ∏ a,
            generalizedConvolution (r + 1) (u a) z := by
  intro m
  induction m with
  | zero =>
      intro u hu
      refine ⟨one r, ?_⟩
      funext z
      simp
  | succ m ih =>
      intro u hu
      obtain ⟨q, hq⟩ :=
        ih (fun a : Fin m => u a.succ)
          (fun a => hu a.succ)
      let p : ConvolutionMixture G (r + 1) :=
        pure (u 0) (hu 0)
      refine ⟨mul r p q, ?_⟩
      funext z
      rw [eval_mul, eval_pure, congrFun hq z,
        Fin.prod_univ_succ]
