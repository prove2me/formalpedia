-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.linearFormsProduct_apCSHeterogeneousOrderedStageFaceExponent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:53:35.724234+00:00
-- url     : https://prove2.me/submissions/341bc14a-aaf9-4af8-b29c-307c37b4e078

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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
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
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators











/-- Selecting a subproduct of one face agrees with selecting the
corresponding subproduct of the full CFZ system. -/
theorem faceSelectedProduct_eq_linearFormsProduct
    (k N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin k) (e : BooleanCube (DeletedCube k j))
    (x : CubePoint k N) :
    cubeSelectedProduct
        (fun ω => faceFactorFamily k N ν j ω x) e =
      linearFormsProduct k N ν
        (faceLinearFormsExponent j e) x := by
  rw [linearFormsProduct, Fintype.prod_eq_single j]
  · simp [cubeSelectedProduct, faceFactorFamily,
      faceLinearFormsExponent]
  · intro j' hj'
    apply Fintype.prod_eq_one
    intro ω
    simp [faceLinearFormsExponent, hj']





























end Wikipedia.SzemeredisTheorem

end
/-!
# Copy-dependent masks in relative counting

The two copies in a projected relative-counting correlation need not have
the same majorant.  This file allows a separate active-face mask

`active : Bool → Fin (n + 1) → Bool`

for each copy.  The corresponding Cauchy--Schwarz stage selector reads the
copy from the distinguished Boolean coordinate of a face vertex.  Thus a
face can retain the `false` copy of `ν`, the `true` copy, both copies, or
neither copy independently.

The stable stage and terminal decoders then give a full structural CFZ
certificate and the usual quantitative root bound.  The final specialization
uses `ν` on the `false` copy and the constant majorant one on the `true`
copy, which is the cross-copy case required by relative counting.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## The copy-dependent AP cut system -/
/-! ## Copy-aware recursive stage selectors -/

open Wikipedia.SzemeredisTheorem in
/-- Pointwise expansion of the copy-aware stage selector. -/
theorem solution
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N) :
    linearFormsProduct (((s + 1) + r) + 1) N ν
        (apCSHeterogeneousOrderedStageFaceExponent
          r s active j) x =
      ∏ bits : Fin (r + 1) → Bool,
        if active (bits 0)
            (apCSOrderedStageCurrentFace r s j)
        then
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j bits) x)
        else 1 := by
  classical
  unfold apCSHeterogeneousOrderedStageFaceExponent
  rw [← faceSelectedProduct_eq_linearFormsProduct]
  unfold cubeSelectedProduct faceFactorFamily
  change
    (∏ ω : DeletedCube
        (((s + 1) + r) + 1)
        (apCSOrderedStageCurrentFace r s j),
      if
        (if ∃ bits : Fin (r + 1) → Bool,
            apCSOrderedStageVertex r s j bits = ω
          then
            active
              (ω (apCSOrderedStageDistinguishedVertexIndex
                r s j))
              (apCSOrderedStageCurrentFace r s j)
          else false)
      then
        ν (apLinearForm
          (((s + 1) + r) + 1) N
          (apCSOrderedStageCurrentFace r s j) ω x)
      else 1) = _
  have hpoint :
      ∀ ω : DeletedCube
          (((s + 1) + r) + 1)
          (apCSOrderedStageCurrentFace r s j),
        (if
          (if ∃ bits : Fin (r + 1) → Bool,
              apCSOrderedStageVertex r s j bits = ω
            then
              active
                (ω (apCSOrderedStageDistinguishedVertexIndex
                  r s j))
                (apCSOrderedStageCurrentFace r s j)
            else false)
        then
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j) ω x)
        else 1) =
          if ∃ bits : Fin (r + 1) → Bool,
              apCSOrderedStageVertex r s j bits = ω
          then
            if active
                (ω (apCSOrderedStageDistinguishedVertexIndex
                  r s j))
                (apCSOrderedStageCurrentFace r s j)
            then
              ν (apLinearForm
                (((s + 1) + r) + 1) N
                (apCSOrderedStageCurrentFace r s j) ω x)
            else 1
          else 1 := by
    intro ω
    by_cases hω :
        ∃ bits : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits = ω
    · simp [hω]
    · simp [hω]
  simp_rw [hpoint]
  rw [← Finset.prod_filter]
  rw [Finset.prod_subtype (F := inferInstance)
    (p := fun ω :
      DeletedCube
        (((s + 1) + r) + 1)
        (apCSOrderedStageCurrentFace r s j) =>
      ∃ bits : Fin (r + 1) → Bool,
        apCSOrderedStageVertex r s j bits = ω)
    (Finset.univ.filter fun ω :
      DeletedCube
        (((s + 1) + r) + 1)
        (apCSOrderedStageCurrentFace r s j) =>
      ∃ bits : Fin (r + 1) → Bool,
        apCSOrderedStageVertex r s j bits = ω)
    (by simp)]
  symm
  apply Fintype.prod_equiv
    (apCSOrderedStageVertexEquiv r s j)
  intro bits
  change
    (if active (bits 0)
          (apCSOrderedStageCurrentFace r s j) then
        ν (apLinearForm
          (((s + 1) + r) + 1) N
          (apCSOrderedStageCurrentFace r s j)
          (apCSOrderedStageVertex r s j bits) x)
      else 1) =
      if active
          (apCSOrderedStageVertex r s j bits
            (apCSOrderedStageDistinguishedVertexIndex
              r s j))
          (apCSOrderedStageCurrentFace r s j)
      then
        ν (apLinearForm
          (((s + 1) + r) + 1) N
          (apCSOrderedStageCurrentFace r s j)
          (apCSOrderedStageVertex r s j bits) x)
      else 1
  rw [apCSOrderedStageVertex_distinguished]
