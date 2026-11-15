-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.iterNextDecoded_apTwoCopyMasked_majorant_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:55:23.347214+00:00
-- url     : https://prove2.me/submissions/35b4ad46-4045-4180-b0a1-a4619dfa6946

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_iterNextDecoded_majorant_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apTwoCopyMaskedMajorant_stageFactor
import Theorems.Thm_Wikipedia_SzemeredisTheorem_linearFormsProduct_apCSOrderedStageFaceExponent

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
# Mixed projected moments for recursive relative densification

After one colour has been densified, its majorant is the constant function
one.  At the next stage the projected majorant is therefore not the product
of a common `ν` on every incident colour: it is a mixed product, with `ν`
only on the colours which remain sparse and `1` on the colours already
densified.

This file closes that moment gap.  A Boolean mask records the remaining
sparse colours.  We expand the first and second moments of the corresponding
projected majorant as explicit subproducts of the original CFZ linear-forms
system.  Consequently one unchanged `HasLinearFormsCondition` supplies the
moment package for every recursive mask, and hence supplies the next
heterogeneous full-to-projected state transition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Majorants with previously densified colours set to one -/



@[simp]
theorem apMaskedFaceMajorant_of_active
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool)
    (i : Fin k) (z : ZMod N)
    (hi : active i = true) :
    apMaskedFaceMajorant ν active i z = ν z := by
  simp [apMaskedFaceMajorant, hi]

@[simp]
theorem apMaskedFaceMajorant_of_inactive
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool)
    (i : Fin k) (z : ZMod N)
    (hi : active i = false) :
    apMaskedFaceMajorant ν active i z = 1 := by
  simp [apMaskedFaceMajorant, hi]







/-! ## Masked CFZ selectors -/









/-! ## Exact mixed projected moments -/





/-! ## The recursive moment and state-transition certificates -/





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
theorem csOrderedStageFactorInput_zero
    {G : Type u} (s : ℕ)
    (a : Fin 0 → G) (z : Fin s → G) :
    csOrderedStageFactorInput 0 s a z = z :=
  rfl













/-! ## Closed formula for an iterated designated majorant -/

namespace MajorizedCutSystem





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
/-! ## The selected stage vertices -/
/-! ## Transport from recursive to geometric coordinate order -/
/-! ## The same selector in recursive arity order -/

open Wikipedia.SzemeredisTheorem in
/-- Successor-stage pointwise identity in the original recursive arity.
The transported distinguished coordinate and active mask are both
explicit, while `j'` is the current non-distinguished face
`j.succAbove ⟨r, _⟩`. -/
theorem solution
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (x : CubePoint (((s + 1) + r) + 1) N) :
    (MajorizedCutSystem.iterNextDecoded
        (apTwoCopyMaskedMajorizedCutSystem
          ((s + 1) + r) N ν active g j hrest)).majorant
        ((apCSOrderedStageCubeEquiv
          r s N j x).1.1.base,
          (apCSOrderedStageCubeEquiv
            r s N j x).1.1.pair)
        0
        (apCSOrderedStageCubeEquiv
          r s N j x).1.2 =
      linearFormsProduct (((s + 1) + r) + 1) N ν
        (apCSOrderedStageFaceExponent
          r s active j) x := by
  classical
  rw [
    MajorizedCutSystem.iterNextDecoded_majorant_zero]
  rw [linearFormsProduct_apCSOrderedStageFaceExponent]
  cases hactive :
      active (apCSOrderedStageCurrentFace r s j) with
  | false =>
      apply Fintype.prod_eq_one
      intro bits
      rw [apTwoCopyMaskedMajorant_stageFactor]
      apply Fintype.prod_eq_one
      intro b
      exact apMaskedFaceMajorant_of_inactive
        ν active
        (apCSOrderedStageCurrentFace r s j) _ hactive
  | true =>
      simp only [if_true]
      simp_rw [apTwoCopyMaskedMajorant_stageFactor]
      simp_rw [apMaskedFaceMajorant_of_active
        ν active
        (apCSOrderedStageCurrentFace r s j) _ hactive]
      let F :
          Bool → (Fin r → Bool) → ℝ :=
        fun b bits =>
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j
              (Fin.cons b bits)) x)
      have hreindex :
          (∏ bits : Fin (r + 1) → Bool,
            ν (apLinearForm
              (((s + 1) + r) + 1) N
              (apCSOrderedStageCurrentFace r s j)
              (apCSOrderedStageVertex r s j bits) x)) =
            ∏ q : Bool × (Fin r → Bool),
              F q.1 q.2 := by
        apply Fintype.prod_equiv
          (Fin.consEquiv
            (fun _ : Fin (r + 1) => Bool)).symm
        intro bits
        rfl
      rw [hreindex, Fintype.prod_prod_type]
      rw [Finset.prod_comm]
