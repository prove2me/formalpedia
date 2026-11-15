-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.abs_form_pow_two_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:23:50.22226+00:00
-- url     : https://prove2.me/submissions/7a88b0d6-eec6-4583-90a0-12bf608b2c34

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_form_sq_le_headMajorantMean_mul_next_form

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

/-- The majorant moment paid in one step is nonnegative. -/
theorem headMajorantMean_nonneg
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) :
    0 ≤ S.headMajorantMean := by
  unfold headMajorantMean mean₂
  exact mean_nonneg fun p =>
    mean_nonneg fun y => S.majorant_nonneg p 0 y

/-- A uniform upper bound for the current majorant moment gives the
absolute-value form of one recursive weighted Cauchy--Schwarz step. -/
theorem abs_form_sq_le_bound_mul_abs_next_form
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    {B : ℝ} (hB : S.headMajorantMean ≤ B) :
    |S.form| ^ 2 ≤ B * |S.next.form| := by
  calc
    |S.form| ^ 2 = S.form ^ 2 := sq_abs S.form
    _ ≤ S.headMajorantMean * S.next.form :=
      S.form_sq_le_headMajorantMean_mul_next_form
    _ ≤ S.headMajorantMean * |S.next.form| :=
      mul_le_mul_of_nonneg_left
        (le_abs_self S.next.form) S.headMajorantMean_nonneg
    _ ≤ B * |S.next.form| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg S.next.form)





end MajorizedCutSystem

/-! ## Linear-forms certificates for every paid moment -/



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
open Wikipedia.SzemeredisTheorem.MajorizedCutSystem
variable {P G : Type*} {n : ℕ}
/-! ## Quantitative iteration -/

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- Closed quantitative form of the repeated weighted Cauchy--Schwarz
recursion:

`|Q₀|^(2^n) ≤ B^(2^n - 1) E`.

Thus the `n` paid majorant moments occur with total multiplicity
`1 + 2 + ⋯ + 2^(n-1) = 2^n - 1`. -/
theorem solution
    {G : Type u} [Fintype G] {B E : ℝ} (hB0 : 0 ≤ B) :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      (S : MajorizedCutSystem P G n),
      HasRecursiveBounds B E S →
        |S.form| ^ (2 ^ n) ≤ B ^ (2 ^ n - 1) * E := by
  intro P instP n S hS
  induction n generalizing P with
  | zero =>
      simpa [HasRecursiveBounds] using hS
  | succ n ih =>
      change
        S.headMajorantMean ≤ B ∧
          HasRecursiveBounds B E S.next at hS
      have hstep :
          |S.form| ^ 2 ≤ B * |S.next.form| :=
        S.abs_form_sq_le_bound_mul_abs_next_form hS.1
      have hnext :
          |S.next.form| ^ (2 ^ n) ≤
            B ^ (2 ^ n - 1) * E :=
        ih S.next hS.2
      have hexponent :
          2 ^ n + (2 ^ n - 1) = 2 ^ (n + 1) - 1 := by
        have hpow : 0 < 2 ^ n := by positivity
        rw [pow_succ]
        omega
      calc
        |S.form| ^ (2 ^ (n + 1)) =
            (|S.form| ^ 2) ^ (2 ^ n) := by
          rw [pow_succ, mul_comm, pow_mul]
        _ ≤ (B * |S.next.form|) ^ (2 ^ n) :=
          pow_le_pow_left₀ (sq_nonneg _) hstep _
        _ = B ^ (2 ^ n) * |S.next.form| ^ (2 ^ n) := by
          rw [mul_pow]
        _ ≤ B ^ (2 ^ n) *
            (B ^ (2 ^ n - 1) * E) :=
          mul_le_mul_of_nonneg_left hnext (pow_nonneg hB0 _)
        _ = B ^ (2 ^ (n + 1) - 1) * E := by
          rw [← mul_assoc, ← pow_add, hexponent]
