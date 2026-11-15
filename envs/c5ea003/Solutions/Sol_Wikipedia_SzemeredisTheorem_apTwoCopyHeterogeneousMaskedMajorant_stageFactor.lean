-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apTwoCopyHeterogeneousMaskedMajorant_stageFactor
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:53:33.555215+00:00
-- url     : https://prove2.me/submissions/0b0257e2-e9a6-4cfb-8aa9-1588faedda69

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apCSOrderedStageCubeEquiv_futureFalse
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apCSOrderedStageCubeEquiv_processedPair
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apSimplexForm_eq_apLinearForm_csOrderedStageVertex

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



@[simp]
theorem eraseCoordinate_insertNth {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (a : G) (x : Fin n → G) :
    eraseCoordinate i (Fin.insertNth i a x) = x := by
  funext j
  simp only [eraseCoordinate_apply, Fin.insertNth_apply_succAbove]

























































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
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





/-- Replacing a coordinate does not change the deleted vector at that
coordinate. -/
@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*}
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

/-- Inserting a replacement into the erased tuple is `Function.update`. -/
theorem insertNth_eraseCoordinate_eq_update
    {n : ℕ} {G : Type*}
    (i : Fin (n + 1)) (a : G) (x : Fin (n + 1) → G) :
    Fin.insertNth i a (eraseCoordinate i x) =
      Function.update x i a := by
  exact Fin.insertNth_removeNth i a x

/-- Replacing coordinate `t` before inserting the distinguished coordinate
`j` only replaces coordinate `j.succAbove t` of the resulting full tuple. -/
theorem insertNth_insertNth_eraseCoordinate
    {n : ℕ} {G : Type*}
    (j : Fin (n + 2)) (t : Fin (n + 1))
    (a b : G) (y : Fin (n + 1) → G) :
    Fin.insertNth j a
        (Fin.insertNth t b (eraseCoordinate t y)) =
      (Function.update (Fin.insertNth j a y)
        (j.succAbove t) b : Fin (n + 2) → G) := by
  rw [insertNth_eraseCoordinate_eq_update, Fin.insertNth_update]

























end Wikipedia.SzemeredisTheorem

end

section



/-!
# CFZ certificates for projected two-copy correlations

The active-majorant induction in relative counting produces a two-copy
correlation.  The coordinate on the selected face is shared, while the
omitted simplex coordinate has two independent copies.  This file realizes
that correlation as a `MajorizedCutSystem`.

The first part supplies a reusable terminal-value theorem for systems whose
designated majorants are all one.  It identifies the fully iterated
Cauchy--Schwarz endpoint with the box moment of the original core.  Applied
to the centered AP face, the box moment is exactly `faceCenteredProduct`.

The second part defines the concrete two-copy AP cut factors and proves that
their system form is the projected correlation occurring in densification.
For factors bounded by one this gives an explicit, kernel-checked
`HasCFZCertificate`, and hence plugs the exact projected expression into the
weighted Cauchy--Schwarz API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem

/-! ## Terminal values for unit-majorant systems -/











end MajorizedCutSystem

/-! ## The centered AP face as a box core -/





namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## Concrete two-copy AP cut factors -/



/-- Evaluating a reconstructed factor on an erased shared tuple recovers
the two actual incident AP faces. -/
theorem apTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (y : Fin n → ZMod N) :
    apTwoCopyCutTest n N g j a t
        (eraseCoordinate t y) =
      ∏ b : Bool,
        g b (j.succAbove t)
          (apSimplexForm (n + 1) N (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (a b) y)
              (j.succAbove t))) := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      unfold apTwoCopyCutTest
      apply Fintype.prod_congr
      intro b
      rw [insertNth_insertNth_eraseCoordinate]
      rw [deleteCoordinate_update_same]









/-! ## A single paid active face -/

















/-! ## Mixed active-majorant system -/













/-! ## The bounded two-copy certificate -/













end Wikipedia.SzemeredisTheorem

end

section


/-!
# Stage decoders for relative-counting Cauchy--Schwarz recursion

Repeated applications of `MajorizedCutSystem.next` replace an external
parameter `P` by the left-associated tower

`(((P × (G × G)) × (G × G)) × ⋯)`.

The declarations below give this tower a stable stage-indexed name and
identify it with a base parameter together with a Boolean pair for every
coordinate already eliminated.  In the AP application the base parameter
is itself a Boolean pair, belonging to the distinguished omitted face.
Thus stage `r` is canonically a Boolean cube on `r + 1` axes.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The nested parameter tower -/





















/-! ## Boolean-axis form of the AP parameter -/







/-! ## Full AP cube decoder -/







@[simp]
theorem apCSStageCubeEquiv_base
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N) :
    (apCSStageCubeEquiv r s N j x).1.1.base =
      x j := by
  simp [apCSStageCubeEquiv, apProjectionAxesEquiv,
    csStageDeletedAxesEquiv, CSStageParam.base]









/-! ## Expected CFZ selectors at a decoded stage -/













/-! ## Iterating `MajorizedCutSystem.next` -/

namespace MajorizedCutSystem



































end MajorizedCutSystem

/-! ## Quantitative endpoint after the decoded first stage -/



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







/-- Every shortened tuple is the deletion of a full tuple.  Supplying the
value at the restored coordinate avoids any inhabitedness assumption. -/
theorem exists_eraseCoordinate_eq
    {G : Type u} {n : ℕ}
    (i : Fin n) (a : G)
    (z : Fin (n - 1) → G) :
    ∃ y : Fin n → G, eraseCoordinate i y = z := by
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      exact
        ⟨Fin.insertNth i a z,
          eraseCoordinate_insertNth i a z⟩





/-! ## Closed formula for an iterated designated majorant -/

namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## The selected stage vertices -/















/-! ## Transport from recursive to geometric coordinate order -/



















@[simp]
theorem apCSOrderedStageCubeEquiv_base
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N) :
    (apCSOrderedStageCubeEquiv r s N j x).1.1.base =
      x j := by
  simp [apCSOrderedStageCubeEquiv,
    apCSStageCubeTransportEquiv,
    apCSStageTransportJ]







/-! ## The same selector in recursive arity order -/









































end Wikipedia.SzemeredisTheorem

end

section


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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The copy-dependent AP cut system -/



@[simp]
theorem apCopyMaskedFaceMajorant_apply
    {k N : ℕ}
    (ν : ZMod N → ℝ)
    (active : Bool → Fin k → Bool)
    (b : Bool) (i : Fin k) (z : ZMod N) :
    apCopyMaskedFaceMajorant ν active b i z =
      if active b i then ν z else 1 :=
  rfl





/-! ## Copy-aware recursive stage selectors -/





/-! ## Copy-aware paid stage moments -/









/-! ## Copy-aware terminal selector -/







namespace MajorizedCutSystem

















end MajorizedCutSystem

/-! ## Quantitative correlation bounds -/



















/-! ## Arbitrary weighted-simplex factors -/

namespace MajorizedCutSystem



end MajorizedCutSystem

















namespace MajorizedCutSystem



end MajorizedCutSystem

/-! ## Arbitrary-factor quantitative bridge -/









namespace HasLinearFormsCondition







end HasLinearFormsCondition

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
/-! ## Copy-aware paid stage moments -/

open Wikipedia.SzemeredisTheorem in
/-- One original heterogeneous designated cut factor, evaluated on the
decoded stage tuple, is the product over the two copy choices at the
current face. -/
theorem solution
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (x : CubePoint (((s + 1) + r) + 1) N)
    (bits : Fin r → Bool) :
    (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest).majorant
        (apCSOrderedStageCubeEquiv r s N j x).1.1.base
        (csOrderedStageCurrentIndex r s)
        (csOrderedStageFactorInput r s
          (fun i =>
            selectPair
              ((apCSOrderedStageCubeEquiv
                r s N j x).1.1.pair i)
              (bits i))
          (apCSOrderedStageCubeEquiv
            r s N j x).1.2) =
      ∏ b : Bool,
        apCopyMaskedFaceMajorant ν active b
          (apCSOrderedStageCurrentFace r s j)
          (apLinearForm (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j
              (Fin.cons b bits)) x) := by
  let z :=
    csOrderedStageFactorInput r s
      (fun i =>
        selectPair
          ((apCSOrderedStageCubeEquiv
            r s N j x).1.1.pair i)
          (bits i))
      (apCSOrderedStageCubeEquiv
        r s N j x).1.2
  obtain ⟨y, hy⟩ :=
    exists_eraseCoordinate_eq
      (csOrderedStageCurrentIndex r s)
      (0 : ZMod N) z
  have hprocessed :
      (fun i =>
        selectPair
          ((apCSOrderedStageCubeEquiv
            r s N j x).1.1.pair i)
          (bits i)) =
        fun i =>
          x (j.succAbove
            (csOrderedStageProcessedIndex r s i))
            (bits i) := by
    funext i
    rw [apCSOrderedStageCubeEquiv_processedPair]
    cases bits i <;> rfl
  have hfuture :
      (apCSOrderedStageCubeEquiv
          r s N j x).1.2 =
        fun t =>
          x (j.succAbove
            (csOrderedStageFutureIndex r s t))
            false := by
    funext t
    exact apCSOrderedStageCubeEquiv_futureFalse
      r s N j x t
  have hz :
      z =
        csOrderedStageFactorInput r s
          (fun i =>
            x (j.succAbove
              (csOrderedStageProcessedIndex r s i))
              (bits i))
          (fun t =>
            x (j.succAbove
              (csOrderedStageFutureIndex r s t))
              false) := by
    unfold z
    exact congrArg₂
      (csOrderedStageFactorInput r s)
      hprocessed hfuture
  have hy' :
      eraseCoordinate
          (csOrderedStageCurrentIndex r s) y =
        csOrderedStageFactorInput r s
          (fun i =>
            x (j.succAbove
              (csOrderedStageProcessedIndex r s i))
              (bits i))
          (fun t =>
            x (j.succAbove
              (csOrderedStageFutureIndex r s t))
              false) :=
    hy.trans hz
  change
    apTwoCopyCutTest ((s + 1) + r) N
        (apCopyMaskedFaceMajorant ν active)
        j
        (apCSOrderedStageCubeEquiv
          r s N j x).1.1.base
        (csOrderedStageCurrentIndex r s) z =
      _
  rw [← hy]
  rw [apTwoCopyCutTest_eraseCoordinate]
  apply Fintype.prod_congr
  intro b
  rw [apCSOrderedStageCubeEquiv_base]
  apply congrArg
    (apCopyMaskedFaceMajorant ν active b
      (apCSOrderedStageCurrentFace r s j))
  exact
    apSimplexForm_eq_apLinearForm_csOrderedStageVertex
      r s N j x bits b y hy'
