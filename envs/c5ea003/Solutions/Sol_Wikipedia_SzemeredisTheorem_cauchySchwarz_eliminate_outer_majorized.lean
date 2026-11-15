-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cauchySchwarz_eliminate_outer_majorized
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:56:51.985198+00:00
-- url     : https://prove2.me/submissions/21842c6c-656e-4e1e-95dc-0e680750cb34

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_mul_sq_le_majorized

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

/-- A normalized mean over a product type is the corresponding iterated
normalized mean. -/
theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)





end Wikipedia.SzemeredisTheorem

end

section


/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem



/-- The square of a normalized mean is the mean over two independent copies
of the variable. -/
theorem mean_sq_eq_mean_pair_mul
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = mean₂ (fun x y => f x * f y) := by
      unfold mean₂ mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (mean_prod_type fun x y => f x * f y).symm













end Wikipedia.SzemeredisTheorem

end
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
/-- Weighted Cauchy--Schwarz in the form used by one recursive
coordinate-elimination step.  Squaring the inner mean replaces the inner
variable by two independent copies. -/
theorem solution
    {X Y : Type*} [Fintype X] [Fintype Y]
    (u v : X → ℝ) (F : X → Y → ℝ)
    (hu : ∀ x, 0 ≤ u x)
    (huv : ∀ x, u x ≤ v x) :
    mean₂ (fun x y => u x * F x y) ^ 2 ≤
      mean v *
        mean₂ (fun x => fun p : Y × Y =>
          v x * F x p.1 * F x p.2) := by
  have hrewrite :
      mean₂ (fun x y => u x * F x y) =
        mean (fun x => u x * mean (F x)) := by
    unfold mean₂
    apply congrArg mean
    funext x
    exact mean_smul (u x) (F x)
  rw [hrewrite]
  calc
    mean (fun x => u x * mean (F x)) ^ 2 ≤
        mean v *
          mean (fun x => v x * mean (F x) ^ 2) :=
      mean_mul_sq_le_majorized u v (fun x => mean (F x)) hu huv
    _ =
        mean v *
          mean₂ (fun x => fun p : Y × Y =>
            v x * F x p.1 * F x p.2) := by
      apply congrArg (fun z : ℝ => mean v * z)
      unfold mean₂
      apply congrArg mean
      funext x
      calc
        v x * mean (F x) ^ 2 =
            v x *
              mean (fun p : Y × Y =>
                F x p.1 * F x p.2) := by
          rw [mean_sq_eq_mean_pair_mul]
        _ =
            mean (fun p : Y × Y =>
              v x * F x p.1 * F x p.2) := by
          simpa only [smul_eq_mul, mul_assoc] using
            (mean_smul (v x)
              (fun p : Y × Y => F x p.1 * F x p.2)).symm
