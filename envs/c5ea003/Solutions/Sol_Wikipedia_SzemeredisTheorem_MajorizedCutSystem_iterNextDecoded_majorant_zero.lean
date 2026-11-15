-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MajorizedCutSystem.iterNextDecoded_majorant_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:40:56.227271+00:00
-- url     : https://prove2.me/submissions/4d688151-46ce-446b-9594-6b12877998e7

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
# Pointwise stage identities for relative counting

This file turns the stage equivalence from
`RelativeCountingDecoder` into closed formulas for the majorants generated
by repeated `MajorizedCutSystem.next`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Prefixing the processed endpoint choices -/





















@[simp]
theorem csOrderedStageFactorInput_zero
    {G : Type u} (s : ℕ)
    (a : Fin 0 → G) (z : Fin s → G) :
    csOrderedStageFactorInput 0 s a z = z :=
  rfl











@[simp]
theorem tail_selectPair_cons
    {G : Type u} {r : ℕ}
    (a : Fin (r + 1) → G × G)
    (b : Bool) (bits : Fin r → Bool) :
    Fin.tail
        (fun i =>
          selectPair (a i)
            ((Fin.cons b bits :
              Fin (r + 1) → Bool) i)) =
      fun i =>
        selectPair (Fin.tail a i) (bits i) := by
  funext i
  rfl

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
/-!
# Pointwise stage identities for relative counting

This file turns the stage equivalence from
`RelativeCountingDecoder` into closed formulas for the majorants generated
by repeated `MajorizedCutSystem.next`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Prefixing the processed endpoint choices -/
/-! ## Closed formula for an iterated designated majorant -/
open Wikipedia.SzemeredisTheorem.MajorizedCutSystem

open Wikipedia.SzemeredisTheorem.MajorizedCutSystem in
/-- After `r` recursive Cauchy--Schwarz steps, the current designated
majorant is the product of the original current-coordinate majorant over
all Boolean choices of the `r` processed endpoint pairs. -/
theorem solution
    {P G : Type u}
    (r s : ℕ)
    (S : MajorizedCutSystem P G ((s + 1) + r))
    (p : P) (a : Fin r → G × G)
    (z : Fin s → G) :
    (iterNextDecoded S).majorant (p, a) 0 z =
      ∏ bits : Fin r → Bool,
        S.majorant p
          (csOrderedStageCurrentIndex r s)
          (csOrderedStageFactorInput r s
            (fun i => selectPair (a i) (bits i)) z) := by
  induction r generalizing P with
  | zero =>
      have hdecode :
          (csStageParamEquiv P G 0).symm (p, a) = p := by
        exact congrArg Prod.fst
          ((csStageParamEquiv P G 0).apply_symm_apply (p, a))
      simp [iterNextDecoded, iterNext, reindex,
        csOrderedStageCurrentIndex, hdecode]
  | succ r ih =>
      change
        (iterNextDecoded S.next).majorant
            ((p, a 0), Fin.tail a) 0 z =
          ∏ bits : Fin (r + 1) → Bool,
            S.majorant p
              (csOrderedStageCurrentIndex (r + 1) s)
              (csOrderedStageFactorInput (r + 1) s
                (fun i =>
                  selectPair (a i) (bits i)) z)
      rw [ih S.next (p, a 0) (Fin.tail a)]
      have hpoint (bits : Fin r → Bool) :
          S.next.majorant (p, a 0)
              (csOrderedStageCurrentIndex r s)
              (csOrderedStageFactorInput r s
                (fun i =>
                  selectPair (Fin.tail a i) (bits i)) z) =
            S.majorant p
                (csOrderedStageCurrentIndex (r + 1) s)
                (csOrderedStageFactorInput (r + 1) s
                  (fun i =>
                    selectPair (a i)
                      ((Fin.cons (false : Bool) bits :
                        Fin (r + 1) → Bool) i)) z) *
              S.majorant p
                (csOrderedStageCurrentIndex (r + 1) s)
                (csOrderedStageFactorInput (r + 1) s
                  (fun i =>
                    selectPair (a i)
                      ((Fin.cons (true : Bool) bits :
                        Fin (r + 1) → Bool) i)) z) := by
        rw [next_majorant_apply]
        apply congrArg₂ (· * ·)
        · apply congrArg₂
            (fun i x => S.majorant p i x)
          · apply Fin.ext
            rfl
          · funext q
            simp [csOrderedStageFactorInput,
              csConsInput]
        · apply congrArg₂
            (fun i x => S.majorant p i x)
          · apply Fin.ext
            rfl
          · funext q
            simp [csOrderedStageFactorInput,
              csConsInput]
      simp_rw [hpoint]
      rw [Finset.prod_mul_distrib]
      let F : Bool → (Fin r → Bool) → ℝ :=
        fun b bits =>
          S.majorant p
            (csOrderedStageCurrentIndex (r + 1) s)
            (csOrderedStageFactorInput (r + 1) s
              (fun i =>
                selectPair (a i)
                  ((Fin.cons b bits :
                    Fin (r + 1) → Bool) i)) z)
      have hreindex :
          (∏ bits : Fin (r + 1) → Bool,
              S.majorant p
                (csOrderedStageCurrentIndex (r + 1) s)
                (csOrderedStageFactorInput (r + 1) s
                  (fun i =>
                    selectPair (a i) (bits i)) z)) =
            ∏ q : Bool × (Fin r → Bool),
              F q.1 q.2 := by
        apply Fintype.prod_equiv
          (Fin.consEquiv
            (fun _ : Fin (r + 1) => Bool)).symm
        intro bits
        rfl
      rw [hreindex]
      rw [Fintype.prod_prod_type]
      rw [Fintype.prod_bool]
      ac_rfl
