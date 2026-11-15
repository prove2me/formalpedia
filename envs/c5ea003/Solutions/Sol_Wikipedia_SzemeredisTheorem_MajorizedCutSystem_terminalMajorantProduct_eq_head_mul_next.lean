-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.terminalMajorantProduct_eq_head_mul_next
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:41:19.133408+00:00
-- url     : https://prove2.me/submissions/c65fdbc2-293a-4c8c-bccd-f69e8f4b47bb

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedFaceCutClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingCertificate
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoder
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderTerminal
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
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
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

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
# Pointwise stage identities for relative counting

This file turns the stage equivalence from
`RelativeCountingDecoder` into closed formulas for the majorants generated
by repeated `MajorizedCutSystem.next`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Prefixing the processed endpoint choices -/



































/-! ## Closed formula for an iterated designated majorant -/

namespace MajorizedCutSystem

/-- The designated majorant field of `next`, uniformly across its
dimension-pattern branches. -/
@[simp]
theorem next_majorant_apply
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (a : G × G)
    (i : Fin n) (z : Fin (n - 1) → G) :
    S.next.majorant (p, a) i z =
      S.majorant p i.succ (csConsInput n a.1 z) *
        S.majorant p i.succ (csConsInput n a.2 z) := by
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ _ =>
      rfl



end MajorizedCutSystem

/-! ## The selected stage vertices -/















/-! ## Transport from recursive to geometric coordinate order -/



























/-! ## The same selector in recursive arity order -/









































end Wikipedia.SzemeredisTheorem

end

section


/-!
# Terminal identities for the relative-counting decoder

This file closes the algebraic end of the mixed Cauchy--Schwarz recursion.
After every deleted coordinate has been doubled, the nested parameter is a
full Boolean AP cube.  The terminal core consists of the centered product
on the distinguished face and one copy of every vertex on each active
non-distinguished face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem







@[simp]
theorem terminalMajorantProduct_zero
    {P G : Type u}
    (S : MajorizedCutSystem P G 0)
    (p : P) (a : Fin 0 → G × G) :
    terminalMajorantProduct S p a = 1 :=
  rfl

@[simp]
theorem terminalMajorantProduct_succ
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (a : Fin (n + 1) → G × G) :
    terminalMajorantProduct S p a =
      ∏ i : Fin (n + 1),
        ∏ bits : Fin n → Bool,
          S.majorant p i
            (eraseCoordinate i
              (fun q =>
                selectPair (a q)
                  (@Fin.insertNth n
                    (fun _ => Bool) i false bits q))) :=
  rfl

































end MajorizedCutSystem

/-! ## The terminal AP cube and its face vertices -/



















namespace MajorizedCutSystem

























end MajorizedCutSystem

/-! ## Quantitative active-mask endpoint -/



end Wikipedia.SzemeredisTheorem

end
/-!
# Terminal identities for the relative-counting decoder

This file closes the algebraic end of the mixed Cauchy--Schwarz recursion.
After every deleted coordinate has been doubled, the nested parameter is a
full Boolean AP cube.  The terminal core consists of the centered product
on the distinguished face and one copy of every vertex on each active
non-distinguished face.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
open Wikipedia.SzemeredisTheorem.MajorizedCutSystem

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- The symmetric terminal majorant product splits into the original head
face and the terminal majorant product of `next`. -/
theorem solution
    {P G : Type u} :
    ∀ {n : ℕ}
      (S : MajorizedCutSystem P G (n + 1))
      (p : P) (a : Fin (n + 1) → G × G),
      terminalMajorantProduct S p a =
        (∏ bits : Fin n → Bool,
          S.majorant p 0
            (fun i =>
              selectPair (Fin.tail a i) (bits i))) *
          terminalMajorantProduct S.next
            (p, a 0) (Fin.tail a) := by
  intro n
  cases n with
  | zero =>
      intro S p a
      rw [terminalMajorantProduct_succ,
        terminalMajorantProduct_zero, mul_one]
      rw [Fin.prod_univ_succ]
      simp only [Finset.univ_eq_empty,
        Finset.prod_empty, mul_one]
      apply Fintype.prod_congr
      intro bits
      apply congrArg (S.majorant p 0)
      funext q
      exact Fin.elim0 q
  | succ n =>
      intro S p a
      rw [terminalMajorantProduct_succ,
        terminalMajorantProduct_succ]
      rw [Fin.prod_univ_succ]
      apply congrArg₂ (· * ·)
      · apply Fintype.prod_congr
        intro bits
        apply congrArg (S.majorant p 0)
        funext q
        apply congrArg₂ selectPair
        · apply congrArg a
          apply Fin.ext
          rfl
        · rfl
      · apply Fintype.prod_congr
        intro i
        simp_rw [next_majorant_apply]
        rw [Finset.prod_mul_distrib]
        let F : Bool → (Fin n → Bool) → ℝ :=
          fun b bits =>
            S.majorant p i.succ
              (Fin.cons (selectPair (a 0) b)
                (eraseCoordinate i
                  (fun q =>
                    selectPair (Fin.tail a q)
                      (@Fin.insertNth n
                        (fun _ => Bool) i false bits q))))
        have hreindex :
            (∏ bits : Fin (n + 1) → Bool,
                S.majorant p i.succ
                  (eraseCoordinate i.succ
                    (fun q =>
                      selectPair (a q)
                        (@Fin.insertNth (n + 1)
                          (fun _ => Bool) i.succ
                            false bits q)))) =
              ∏ q : Bool × (Fin n → Bool),
                F q.1 q.2 := by
          apply Fintype.prod_equiv
            (Fin.consEquiv
              (fun _ : Fin (n + 1) => Bool)).symm
          intro bits
          apply congrArg (S.majorant p i.succ)
          have hinsert :
              (@Fin.insertNth (n + 1)
                (fun _ => Bool) i.succ false bits) =
                Fin.cons (bits 0)
                  (@Fin.insertNth n
                    (fun _ => Bool) i false
                      (Fin.tail bits)) := by
            rw [← Fin.cons_self_tail bits]
            exact Fin.insertNth_succ_cons
              i false (bits 0) (Fin.tail bits)
          rw [show
            (fun q =>
              selectPair (a q)
                (@Fin.insertNth (n + 1)
                  (fun _ => Bool) i.succ false
                    bits q)) =
              Fin.cons (selectPair (a 0) (bits 0))
                (fun q =>
                  selectPair (Fin.tail a q)
                    (@Fin.insertNth n
                      (fun _ => Bool) i false
                        (Fin.tail bits) q)) by
              rw [hinsert]
              funext q
              refine Fin.cases ?_ (fun t => ?_) q
              · rfl
              · rfl]
          exact eraseCoordinate_succ_cons i _ _
        rw [hreindex, Fintype.prod_prod_type,
          Fintype.prod_bool]
        simp [F, csConsInput]
        ring
