-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apSimplexForm_eq_apLinearForm_terminalFaceVertex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:45:36.328555+00:00
-- url     : https://prove2.me/submissions/bea51a90-b9e8-4362-9165-54bdbbd0dc62

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











































end MajorizedCutSystem

/-! ## The terminal AP cube and its face vertices -/



@[simp]
theorem apCSTerminalCubeEquiv_apply_distinguished
    (n N : ℕ) (j : Fin (n + 1))
    (p : (Bool → ZMod N) ×
      (Fin n → ZMod N × ZMod N))
    (b : Bool) :
    apCSTerminalCubeEquiv n N j p j b =
      p.1 b := by
  simp [apCSTerminalCubeEquiv]

@[simp]
theorem apCSTerminalCubeEquiv_apply_succAbove
    (n N : ℕ) (j : Fin (n + 1))
    (p : (Bool → ZMod N) ×
      (Fin n → ZMod N × ZMod N))
    (t : Fin n) (b : Bool) :
    apCSTerminalCubeEquiv n N j p
        (j.succAbove t) b =
      selectPair (p.2 t) b := by
  simp [apCSTerminalCubeEquiv]





@[simp]
theorem apCSTerminalFaceVertex_distinguished
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (bits : Bool × (Fin m → Bool)) :
    apCSTerminalFaceVertex m j t bits
        ⟨j, (Fin.succAbove_ne j t).symm⟩ =
      bits.1 :=
  congrArg Prod.fst
    ((apCSTerminalFaceVertexEquiv
      m j t).left_inv bits)

@[simp]
theorem apCSTerminalFaceVertex_other
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (bits : Bool × (Fin m → Bool))
    (r : Fin m) :
    apCSTerminalFaceVertex m j t bits
        ⟨j.succAbove (t.succAbove r), by
          intro h
          exact (Fin.succAbove_ne t r)
            (Fin.succAbove_right_injective h)⟩ =
      bits.2 r :=
  congrFun
    (congrArg Prod.snd
      ((apCSTerminalFaceVertexEquiv
        m j t).left_inv bits)) r





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
/-! ## The terminal AP cube and its face vertices -/

open Wikipedia.SzemeredisTheorem in
/-- The AP simplex form reconstructed by a terminal majorant is the CFZ
linear form at the corresponding full terminal face vertex. -/
theorem solution
    (m N : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (p : Bool → ZMod N)
    (a : Fin (m + 1) → ZMod N × ZMod N)
    (b : Bool) (bits : Fin m → Bool) :
    apSimplexForm ((m + 1) + 1) N
        (j.succAbove t)
        (deleteCoordinate
          (Fin.insertNth j (p b)
            (fun q =>
              selectPair (a q)
                (@Fin.insertNth m
                  (fun _ => Bool) t false bits q)))
          (j.succAbove t)) =
      apLinearForm ((m + 1) + 1) N
        (j.succAbove t)
        (apCSTerminalFaceVertex
          m j t (b, bits))
        (apCSTerminalCubeEquiv
          (m + 1) N j (p, a)) := by
  unfold apSimplexForm apLinearForm
  apply Fintype.sum_congr
  intro q
  apply congrArg
    (fun z : ZMod N =>
      ((((q.1 : ℤ) -
        (j.succAbove t : ℤ) : ℤ) :
          ZMod N) * z))
  change
    (@Fin.insertNth (m + 1)
      (fun _ => ZMod N) j (p b)
      (fun q =>
        selectPair (a q)
          (@Fin.insertNth m
            (fun _ => Bool) t false bits q))) q.1 =
      apCSTerminalCubeEquiv
          (m + 1) N j (p, a) q.1
        (apCSTerminalFaceVertex
          m j t (b, bits) q)
  by_cases hq : q.1 = j
  · have hqeq :
        q = ⟨j, (Fin.succAbove_ne j t).symm⟩ := by
      apply Subtype.ext
      exact hq
    rw [hqeq]
    simp
  · let d :=
      (Wikipedia.SzemeredisTheorem.finSuccAboveEquiv j).symm
        ⟨q.1, hq⟩
    have hjd : j.succAbove d = q.1 := by
      exact congrArg Subtype.val
        ((Wikipedia.SzemeredisTheorem.finSuccAboveEquiv j).apply_symm_apply
          ⟨q.1, hq⟩)
    have hdt : d ≠ t := by
      intro h
      apply q.2
      rw [← hjd, h]
    let r :=
      (Wikipedia.SzemeredisTheorem.finSuccAboveEquiv t).symm
        ⟨d, hdt⟩
    have htr : t.succAbove r = d := by
      exact congrArg Subtype.val
        ((Wikipedia.SzemeredisTheorem.finSuccAboveEquiv t).apply_symm_apply
          ⟨d, hdt⟩)
    have hqeq :
        q =
          ⟨j.succAbove (t.succAbove r), by
            intro h
            exact (Fin.succAbove_ne t r)
              (Fin.succAbove_right_injective h)⟩ := by
      apply Subtype.ext
      change q.1 = j.succAbove (t.succAbove r)
      rw [htr, hjd]
    rw [hqeq]
    simp
