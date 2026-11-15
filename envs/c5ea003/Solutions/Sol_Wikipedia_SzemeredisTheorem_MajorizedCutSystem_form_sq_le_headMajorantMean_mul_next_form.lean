-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.form_sq_le_headMajorantMean_mul_next_form
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:22:29.05166+00:00
-- url     : https://prove2.me/submissions/3a9d1b44-f6a0-4c4b-8965-c8e940babf55

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_form_succ
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cauchySchwarz_eliminate_outer_majorized

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







/-- Fubini in the form which moves the middle variable across a product
parameter.  This is the bookkeeping identity needed after a coordinate has
been duplicated. -/
theorem mean_prod_swap_middle
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → C → ℝ) :
    mean₂ (fun q : A × B => fun c => F q.1 q.2 c) =
      mean₂ (fun q : A × C => fun b => F q.1 b q.2) := by
  change
    mean (fun q : A × B => mean (fun c => F q.1 q.2 c)) =
      mean (fun q : A × C => mean (fun b => F q.1 b q.2))
  rw [mean_prod_type
        (fun a : A => fun b : B => mean (fun c : C => F a b c)),
      mean_prod_type
        (fun a : A => fun c : C => mean (fun b : B => F a b c))]
  apply congrArg mean
  funext a
  exact mean₂_comm (F a)

/-! ## Parameterized majorized cut systems -/



namespace MajorizedCutSystem

variable {P G : Type*} {n : ℕ}















/-- The two copies of the tail integrand, together with the paid head
majorant, are exactly the integrand of the transformed cut system. -/
theorem tailIntegrand_pair
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (y : Fin n → G) (a : G × G) :
    S.majorant p 0 y *
          S.tailIntegrand p y a.1 *
          S.tailIntegrand p y a.2 =
      S.next.core (p, a) y *
        ∏ i, S.next.factor (p, a) i
          (eraseCoordinate i y) := by
  cases n with
  | zero =>
      simp [tailIntegrand, next]
  | succ n =>
      simp only [tailIntegrand, next]
      simp only [eraseCoordinate_succ_cons]
      rw [Finset.prod_mul_distrib]
      ac_rfl



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
/-- One CFZ weighted Cauchy--Schwarz step.  The head factor is enlarged to
its designated majorant, the head coordinate is duplicated, and all
remaining factors are paired. -/
theorem solution
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) :
    S.form ^ 2 ≤ S.headMajorantMean * S.next.form := by
  rw [S.form_succ]
  calc
    mean₂ (fun q : P × (Fin n → G) => fun a : G =>
        S.factor q.1 0 q.2 *
          S.tailIntegrand q.1 q.2 a) ^ 2 ≤
        mean (fun q : P × (Fin n → G) =>
          S.majorant q.1 0 q.2) *
          mean₂ (fun q : P × (Fin n → G) => fun a : G × G =>
            S.majorant q.1 0 q.2 *
              S.tailIntegrand q.1 q.2 a.1 *
              S.tailIntegrand q.1 q.2 a.2) := by
      exact cauchySchwarz_eliminate_outer_majorized
        (fun q : P × (Fin n → G) => S.factor q.1 0 q.2)
        (fun q : P × (Fin n → G) => S.majorant q.1 0 q.2)
        (fun q : P × (Fin n → G) => fun a : G =>
          S.tailIntegrand q.1 q.2 a)
        (fun q => S.factor_nonneg q.1 0 q.2)
        (fun q => S.factor_le_majorant q.1 0 q.2)
    _ = S.headMajorantMean *
        mean₂ (fun q : P × (G × G) => fun y : Fin n → G =>
          S.majorant q.1 0 y *
            S.tailIntegrand q.1 y q.2.1 *
            S.tailIntegrand q.1 y q.2.2) := by
      apply congrArg₂ (· * ·)
      · change
          mean (fun q : P × (Fin n → G) =>
            S.majorant q.1 0 q.2) =
            mean₂ (fun p : P => fun y : Fin n → G =>
              S.majorant p 0 y)
        exact mean_prod_type
          (fun p : P => fun y : Fin n → G =>
            S.majorant p 0 y)
      · exact mean_prod_swap_middle
          (A := P) (B := Fin n → G) (C := G × G)
          (fun p y a =>
            S.majorant p 0 y *
              S.tailIntegrand p y a.1 *
              S.tailIntegrand p y a.2)
    _ = S.headMajorantMean * S.next.form := by
      apply congrArg (fun z : ℝ => S.headMajorantMean * z)
      unfold form mean₂
      apply congrArg mean
      funext q
      apply congrArg mean
      funext y
      exact S.tailIntegrand_pair q.1 y q.2
