-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apSimplexForm_eq_apLinearForm_csOrderedStageVertex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:52:32.559288+00:00
-- url     : https://prove2.me/submissions/f8f090e7-01e5-4528-9abf-5175e93674ce

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_eraseCoordinate_preimage

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
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















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













@[simp]
theorem csConsInput_apply_zero
    {G : Type u} (n : ℕ) (hn : 0 < n)
    (a : G) (z : Fin (n - 1) → G) :
    csConsInput n a z ⟨0, hn⟩ = a := by
  cases n with
  | zero => omega
  | succ _ => rfl

@[simp]
theorem csConsInput_apply_succ
    {G : Type u} (n : ℕ)
    (a : G) (z : Fin (n - 1) → G)
    (i : Fin (n - 1)) :
    csConsInput n a z ⟨i + 1, by omega⟩ =
      z i := by
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ _ =>
      rfl





@[simp]
theorem csOrderedStageFactorInput_zero
    {G : Type u} (s : ℕ)
    (a : Fin 0 → G) (z : Fin s → G) :
    csOrderedStageFactorInput 0 s a z = z :=
  rfl

@[simp]
theorem csOrderedStageFactorInput_succ
    {G : Type u} (r s : ℕ)
    (a : Fin (r + 1) → G) (z : Fin s → G) :
    csOrderedStageFactorInput (r + 1) s a z =
      csConsInput ((s + 1) + r) (a 0)
        (csOrderedStageFactorInput r s
          (Fin.tail a) z) :=
  rfl

@[simp]
theorem csOrderedStageFactorInput_processed
    {G : Type u} (r s : ℕ)
    (a : Fin r → G) (z : Fin s → G)
    (i : Fin r) :
    csOrderedStageFactorInput r s a z
        ⟨i, by omega⟩ =
      a i := by
  induction r with
  | zero =>
      exact Fin.elim0 i
  | succ r ih =>
      refine Fin.cases ?_ (fun q => ?_) i
      · rw [csOrderedStageFactorInput_succ]
        exact csConsInput_apply_zero
          ((s + 1) + r) (by omega) _ _
      · rw [csOrderedStageFactorInput_succ]
        let q' : Fin (((s + 1) + r) - 1) :=
          ⟨q, by omega⟩
        calc
          csConsInput ((s + 1) + r) (a 0)
              (csOrderedStageFactorInput r s
                (Fin.tail a) z) ⟨q + 1, by omega⟩ =
              csOrderedStageFactorInput r s
                (Fin.tail a) z q' := by
                exact csConsInput_apply_succ
                  ((s + 1) + r) (a 0)
                  (csOrderedStageFactorInput r s
                    (Fin.tail a) z) q'
          _ = Fin.tail a q := by
            exact ih (Fin.tail a) q
          _ = a q.succ := rfl

@[simp]
theorem csOrderedStageFactorInput_future
    {G : Type u} (r s : ℕ)
    (a : Fin r → G) (z : Fin s → G)
    (t : Fin s) :
    csOrderedStageFactorInput r s a z
        ⟨r + t, by omega⟩ =
      z t := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [csOrderedStageFactorInput_succ]
      let q : Fin (((s + 1) + r) - 1) :=
        ⟨r + t, by omega⟩
      have hcons :=
        csConsInput_apply_succ
          ((s + 1) + r) (a 0)
          (csOrderedStageFactorInput r s
            (Fin.tail a) z) q
      calc
        csConsInput ((s + 1) + r) (a 0)
            (csOrderedStageFactorInput r s
              (Fin.tail a) z)
            ⟨(r + 1) + t, by omega⟩ =
            csOrderedStageFactorInput r s
              (Fin.tail a) z q := by
                rw [show
                  (⟨(r + 1) + t, by omega⟩ :
                    Fin ((s + 1) + r)) =
                    ⟨q + 1, by omega⟩ by
                      apply Fin.ext
                      simp [q]
                      omega]
                exact hcons
        _ = z t := ih (Fin.tail a)







/-! ## Closed formula for an iterated designated majorant -/

namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## The selected stage vertices -/















/-! ## Transport from recursive to geometric coordinate order -/



























/-! ## The same selector in recursive arity order -/















@[simp]
theorem apCSOrderedStageVertex_future
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool)
    (t : Fin s) :
    apCSOrderedStageVertex r s j bits
        (apCSOrderedStageFutureVertexIndex r s j t) =
      false := by
  unfold apCSOrderedStageVertex
  rw [dif_neg]
  · dsimp only [apCSOrderedStageFutureVertexIndex]
    have ht :
        (finSuccAboveEquiv j).symm
            ⟨j.succAbove
                (csOrderedStageFutureIndex r s t),
              Fin.succAbove_ne j
                (csOrderedStageFutureIndex r s t)⟩ =
          csOrderedStageFutureIndex r s t :=
      (finSuccAboveEquiv j).symm_apply_apply
        (csOrderedStageFutureIndex r s t)
    rw [ht]
    rw [dif_neg]
    simp
    simp [csOrderedStageFutureIndex]
    omega
  · exact Fin.succAbove_ne j
      (csOrderedStageFutureIndex r s t)

























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
/-! ## The selected stage vertices -/
/-! ## Transport from recursive to geometric coordinate order -/
/-! ## The same selector in recursive arity order -/

open Wikipedia.SzemeredisTheorem in
/-- The reconstructed current-face AP form is the CFZ form at the
corresponding ordered-stage Boolean vertex. -/
theorem solution
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N)
    (bits : Fin r → Bool) (b : Bool)
    (y : Fin ((s + 1) + r) → ZMod N)
    (hy :
      eraseCoordinate (csOrderedStageCurrentIndex r s) y =
        csOrderedStageFactorInput r s
          (fun i =>
            x (j.succAbove
              (csOrderedStageProcessedIndex r s i))
              (bits i))
          (fun t =>
            x (j.succAbove
              (csOrderedStageFutureIndex r s t))
              false)) :
    apSimplexForm (((s + 1) + r) + 1) N
        (apCSOrderedStageCurrentFace r s j)
        (deleteCoordinate
          (Fin.insertNth j (x j b) y)
          (apCSOrderedStageCurrentFace r s j)) =
      apLinearForm (((s + 1) + r) + 1) N
        (apCSOrderedStageCurrentFace r s j)
        (apCSOrderedStageVertex r s j
          (Fin.cons b bits)) x := by
  unfold apSimplexForm apLinearForm
  apply Fintype.sum_congr
  intro i
  apply congrArg
    (fun z : ZMod N =>
      ((((i.1 : ℤ) -
        (apCSOrderedStageCurrentFace r s j : ℤ) : ℤ) :
          ZMod N) * z))
  change
    (@Fin.insertNth ((s + 1) + r)
      (fun _ => ZMod N) j (x j b) y i.1) =
      x i.1
        (apCSOrderedStageVertex r s j
          (Fin.cons b bits) i)
  by_cases hij : i.1 = j
  · rw [hij]
    simp only [Fin.insertNth_apply_same]
    unfold apCSOrderedStageVertex
    rw [dif_pos hij]
    rfl
  · let t :=
      (Wikipedia.SzemeredisTheorem.finSuccAboveEquiv j).symm
        ⟨i.1, hij⟩
    have hjt :
        j.succAbove t = i.1 := by
      have h :=
        congrArg Subtype.val
          ((Wikipedia.SzemeredisTheorem.finSuccAboveEquiv j).apply_symm_apply
            ⟨i.1, hij⟩)
      exact h
    have htne :
        t ≠ csOrderedStageCurrentIndex r s := by
      intro ht
      apply i.2
      rw [← hjt, ht]
      rfl
    obtain ⟨q, hqy, hval⟩ :=
      exists_eraseCoordinate_preimage
        (csOrderedStageCurrentIndex r s) t htne y
    have hfactor :
        csOrderedStageFactorInput r s
            (fun p =>
              x (j.succAbove
                (csOrderedStageProcessedIndex r s p))
                (bits p))
            (fun u =>
              x (j.succAbove
                (csOrderedStageFutureIndex r s u))
                false) q =
          y t :=
      (congrFun hy q).symm.trans hqy
    have hinsert :
        (@Fin.insertNth ((s + 1) + r)
          (fun _ => ZMod N) j (x j b) y i.1) =
          y t := by
      rw [← hjt]
      simp
    rw [hinsert]
    by_cases hq : q.val < r
    · let p : Fin r := ⟨q.val, hq⟩
      have htval : t.val = q.val := by
        simp [csOrderedStageCurrentIndex, hq] at hval
        omega
      have ht :
          t = csOrderedStageProcessedIndex r s p := by
        apply Fin.ext
        simpa [p, csOrderedStageProcessedIndex]
          using htval
      have hi :
          i =
            apCSOrderedStageProcessedVertexIndex
              r s j p := by
        apply Subtype.ext
        change
          i.1 =
            j.succAbove
              (csOrderedStageProcessedIndex r s p)
        rw [← hjt, ht]
      have hqindex :
          q =
            (⟨p.val, by omega⟩ :
              Fin (((s + 1) + r) - 1)) := by
        apply Fin.ext
        rfl
      rw [hi, ← hfactor, hqindex]
      rw [csOrderedStageFactorInput_processed]
      apply congrArg
        (x (j.succAbove
          (csOrderedStageProcessedIndex r s p)))
      symm
      simp
    · let u : Fin s :=
        ⟨q.val - r, by omega⟩
      have htval : t.val = q.val + 1 := by
        simp [csOrderedStageCurrentIndex, hq] at hval
        omega
      have ht :
          t = csOrderedStageFutureIndex r s u := by
        apply Fin.ext
        simp [u, csOrderedStageFutureIndex]
        omega
      have hi :
          i =
            apCSOrderedStageFutureVertexIndex
              r s j u := by
        apply Subtype.ext
        change
          i.1 =
            j.succAbove
              (csOrderedStageFutureIndex r s u)
        rw [← hjt, ht]
      have hqindex :
          q =
            (⟨r + u.val, by omega⟩ :
              Fin (((s + 1) + r) - 1)) := by
        apply Fin.ext
        simp [u]
        omega
      rw [hi, ← hfactor, hqindex]
      rw [csOrderedStageFactorInput_future]
      apply congrArg
        (x (j.succAbove
          (csOrderedStageFutureIndex r s u)))
      exact
        (apCSOrderedStageVertex_future
          r s j (Fin.cons b bits) u).symm
