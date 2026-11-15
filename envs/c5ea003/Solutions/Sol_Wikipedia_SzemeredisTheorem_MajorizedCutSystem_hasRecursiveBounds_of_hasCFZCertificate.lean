-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.hasRecursiveBounds_of_hasCFZCertificate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:56:51.946207+00:00
-- url     : https://prove2.me/submissions/4b4a7f54-e8ff-4028-91fb-b0a9e863fb3f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_abs_mean_faceCenteredProduct_mul_le

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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Weighted finite Cauchy--Schwarz -/









/-! ## Parameterized majorized cut systems -/



namespace MajorizedCutSystem

variable {P G : Type*} {n : ℕ}



















/-! ## Quantitative iteration -/









end MajorizedCutSystem

/-! ## Linear-forms certificates for every paid moment -/

/-- Every CFZ subproduct has mean at most `1 + η`.  This is the
one-sided consequence of the linear-forms condition used to pay the
majorant moments in the repeated Cauchy--Schwarz argument. -/
theorem HasLinearFormsCondition.mean_linearFormsProduct_le_one_add
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    (e : LinearFormsExponent k) :
    mean (linearFormsProduct k N ν e) ≤ 1 + η := by
  have hupper :
      mean (linearFormsProduct k N ν e) - 1 ≤ η :=
    (le_abs_self
      (mean (linearFormsProduct k N ν e) - 1)).trans (hLF e)
  linarith

namespace MajorizedCutSystem



























end MajorizedCutSystem

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
/-! ## Parameterized majorized cut systems -/
/-! ## Linear-forms certificates for every paid moment -/
open Wikipedia.SzemeredisTheorem.MajorizedCutSystem

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- A CFZ certificate discharges all recursive analytic bounds: every
intermediate majorant moment costs at most `1 + η`, and the terminal form
is controlled by the weighted strong-linear-forms endpoint. -/
theorem solution
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      (S : MajorizedCutSystem P G n),
      HasCFZCertificate ν j S →
        HasRecursiveBounds
          (1 + η)
          ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η)
          S := by
  intro P instP n S hS
  induction n generalizing P with
  | zero =>
      rcases hS with ⟨other, hother, hterminal⟩
      change
        |S.form| ≤
          (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η
      rw [hterminal]
      exact hLF.abs_mean_faceCenteredProduct_mul_le
        j other hother
  | succ n ih =>
      rcases hS with ⟨e, hmoment, hnext⟩
      change
        S.headMajorantMean ≤ 1 + η ∧
          HasRecursiveBounds
            (1 + η)
            ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η)
            S.next
      constructor
      · rw [hmoment]
        exact hLF.mean_linearFormsProduct_le_one_add e
      · exact ih S.next hnext
