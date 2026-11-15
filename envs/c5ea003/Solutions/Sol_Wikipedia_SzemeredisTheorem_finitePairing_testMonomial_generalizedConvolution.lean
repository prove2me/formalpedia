-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.finitePairing_testMonomial_generalizedConvolution
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:07.486124+00:00
-- url     : https://prove2.me/submissions/36700bb3-8261-431b-bd3e-557257236725

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





/-- A product of normalized means is the normalized mean over an independent
choice of one input for every factor. -/
theorem prod_mean
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β]
    (F : ι → β → ℝ) :
    (∏ i, mean (F i)) =
      mean (fun y : ι → β => ∏ i, F i (y i)) := by
  classical
  simp_rw [mean, Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]
  simp

end Wikipedia.SzemeredisTheorem

end

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
# Moments of generalized convolutions

Products of generalized convolutions are averages over independent copies of
the corresponding sum fibers.  This file records that disintegration
exactly and packages the remaining analytic estimate as a concrete moment
condition.  It is the interface at which iterated Cauchy--Schwarz and the
linear-forms estimate enter the dense-model proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial



/-- Product of generalized convolutions as a single average over independent
fiber variables. -/
theorem prod_generalizedConvolution_succ_eq_mean
    {G ι : Type*} [Fintype G] [AddCommGroup G]
    [Fintype ι] [DecidableEq ι]
    (r : ℕ) (u : ι → CutTestFamily G (r + 1))
    (z : G) :
    (∏ a, generalizedConvolution (r + 1) (u a) z) =
      mean (fun y : ι → (Fin r → G) =>
        ∏ a, cutTestProduct (u a)
          (sumFiberTuple r z (y a))) := by
  simp_rw [generalizedConvolution_succ]
  exact prod_mean fun a y =>
    cutTestProduct (u a) (sumFiberTuple r z y)















end Wikipedia.SzemeredisTheorem

end
/-!
# Moments of generalized convolutions

Products of generalized convolutions are averages over independent copies of
the corresponding sum fibers.  This file records that disintegration
exactly and packages the remaining analytic estimate as a concrete moment
condition.  It is the interface at which iterated Cauchy--Schwarz and the
linear-forms estimate enter the dense-model proof.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial

open Wikipedia.SzemeredisTheorem in
/-- Pairing the centered majorant with a monomial of generalized
convolutions is exactly the expanded fiber moment. -/
theorem solution
    {G τ : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (ν : G → ℝ)
    (u : τ → CutTestFamily G (r + 1))
    {n : ℕ} (s : Fin n → τ) :
    finitePairing (ν - fun _ => 1)
        (testMonomial
          (fun t => generalizedConvolution (r + 1) (u t)) s) =
      convolutionMonomialMoment r ν (fun a => u (s a)) := by
  unfold finitePairing convolutionMonomialMoment mean₂
  apply congrArg mean
  funext z
  change
    (ν z - 1) *
        (∏ a, generalizedConvolution (r + 1) (u (s a)) z) =
      mean (fun y : Fin n → (Fin r → G) =>
        (ν z - 1) *
          ∏ a, cutTestProduct (u (s a))
            (sumFiberTuple r z (y a)))
  rw [prod_generalizedConvolution_succ_eq_mean]
  exact (mean_smul (ν z - 1) _).symm
