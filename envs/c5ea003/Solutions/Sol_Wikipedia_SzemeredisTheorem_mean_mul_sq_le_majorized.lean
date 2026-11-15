-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_mul_sq_le_majorized
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:55:47.756227+00:00
-- url     : https://prove2.me/submissions/b2f5ad4c-43f8-4d94-8025-157e635f7e30

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_mul_sq_le_weighted

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Repeated weighted Cauchy--Schwarz for strong linear forms

This file supplies the recursive analytic bridge which precedes the
algebraic endpoint in `WeightedStrongLinearForms`.

The recursion is the quantitative finite version of Conlon--Fox--Zhao,
Lemma 6.3.  A parameterized cut system consists of a possibly signed core
and one nonnegative factor for every deleted coordinate.  Each factor is
dominated by a designated majorant.  One Cauchy--Schwarz step

* removes the head factor;
* pays the normalized mean of its majorant;
* duplicates the head coordinate;
* pairs every remaining factor; and
* inserts the removed majorant into the new core.

After all coordinates have been processed, the core is the product of all
copies of the original centered factor together with exactly one copy of
each selected face majorant.  No pointwise bound on the majorants is used.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Weighted finite Cauchy--Schwarz -/

open Wikipedia.SzemeredisTheorem in
/-- A nonnegative weight may be enlarged on both factors in the weighted
Cauchy--Schwarz bound. -/
theorem solution
    {Ω : Type*} [Fintype Ω]
    (u v w : Ω → ℝ)
    (hu : ∀ x, 0 ≤ u x)
    (huv : ∀ x, u x ≤ v x) :
    mean (fun x => u x * w x) ^ 2 ≤
      mean v * mean (fun x => v x * w x ^ 2) := by
  have hv : ∀ x, 0 ≤ v x :=
    fun x => (hu x).trans (huv x)
  calc
    mean (fun x => u x * w x) ^ 2 ≤
        mean u * mean (fun x => u x * w x ^ 2) :=
      mean_mul_sq_le_weighted u w hu
    _ ≤ mean v * mean (fun x => v x * w x ^ 2) := by
      exact mul_le_mul
        (mean_mono huv)
        (mean_mono fun x =>
          mul_le_mul_of_nonneg_right (huv x) (sq_nonneg (w x)))
        (mean_nonneg fun x => mul_nonneg (hu x) (sq_nonneg (w x)))
        (mean_nonneg hv)
