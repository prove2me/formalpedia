-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.form_succ
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:26:06.83565+00:00
-- url     : https://prove2.me/submissions/8c2b2f87-95ad-4572-8622-647d7fa3c649

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_fin_cons

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

end Wikipedia.SzemeredisTheorem

end

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
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators











































@[simp]
theorem eraseCoordinate_zero_cons
    {G : Type*} {n : ℕ} (a : G) (y : Fin n → G) :
    eraseCoordinate (0 : Fin (n + 1)) (Fin.cons a y) = y := by
  funext j
  simp [eraseCoordinate_apply]

@[simp]
theorem eraseCoordinate_succ_cons
    {G : Type*} {n : ℕ} (i : Fin (n + 1))
    (a : G) (y : Fin (n + 1) → G) :
    eraseCoordinate i.succ (Fin.cons a y) =
      Fin.cons a (eraseCoordinate i y) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      simp [eraseCoordinate_apply]
  | succ j =>
      simp [eraseCoordinate_apply]























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











/-- Pointwise form of splitting off the head deleted-coordinate factor. -/
theorem integrand_cons
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (y : Fin n → G) (a : G) :
    S.core p (Fin.cons a y) *
          ∏ i, S.factor p i
            (eraseCoordinate i (Fin.cons a y)) =
      S.factor p 0 y * S.tailIntegrand p y a := by
  cases n with
  | zero =>
      simp [tailIntegrand]
      ring_nf
  | succ n =>
      rw [Fin.prod_univ_succ]
      simp only [eraseCoordinate_zero_cons]
      simp [tailIntegrand]
      ring







/-! ## Quantitative iteration -/









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

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- Split a parameterized successor-dimensional form into its head factor
and the remaining inner integrand. -/
theorem solution
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) :
    S.form =
      mean₂ (fun q : P × (Fin n → G) => fun a : G =>
        S.factor q.1 0 q.2 *
          S.tailIntegrand q.1 q.2 a) := by
  unfold form
  calc
    mean₂ (fun p x =>
        S.core p x *
          ∏ i, S.factor p i (eraseCoordinate i x)) =
        mean (fun p =>
          mean₂ (fun a : G => fun y : Fin n → G =>
            S.core p (Fin.cons a y) *
              ∏ i, S.factor p i
                (eraseCoordinate i (Fin.cons a y)))) := by
      unfold mean₂
      apply congrArg mean
      funext p
      exact mean_fin_cons _
    _ = mean (fun p =>
          mean₂ (fun y : Fin n → G => fun a : G =>
            S.core p (Fin.cons a y) *
              ∏ i, S.factor p i
                (eraseCoordinate i (Fin.cons a y)))) := by
      apply congrArg mean
      funext p
      exact mean₂_comm _
    _ = mean₂ (fun q : P × (Fin n → G) => fun a : G =>
          S.core q.1 (Fin.cons a q.2) *
            ∏ i, S.factor q.1 i
              (eraseCoordinate i (Fin.cons a q.2))) := by
      simpa only [mean₂] using
        (mean_prod_type
          (fun p : P => fun y : Fin n → G =>
            mean (fun a : G =>
              S.core p (Fin.cons a y) *
                ∏ i, S.factor p i
                  (eraseCoordinate i (Fin.cons a y))))).symm
    _ = mean₂ (fun q : P × (Fin n → G) => fun a : G =>
          S.factor q.1 0 q.2 *
            S.tailIntegrand q.1 q.2 a) := by
      unfold mean₂
      apply congrArg mean
      funext q
      apply congrArg mean
      funext a
      exact S.integrand_cons q.1 q.2 a
