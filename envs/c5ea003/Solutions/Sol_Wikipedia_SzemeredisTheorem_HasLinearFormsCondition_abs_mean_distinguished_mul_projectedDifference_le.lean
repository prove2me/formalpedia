-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_mean_distinguished_mul_projectedDifference_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:02:21.10653+00:00
-- url     : https://prove2.me/submissions/8258bbf9-f51c-48a6-9d35-5f48bc61482b

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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasProjectedMajorantMoments_mean_projectedDifference_sq_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_abs_form_pow_two_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_hasRecursiveBounds_of_hasCFZCertificate
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_centered_projectedDifference_sq_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_apMaskedProjectedMajorant_sq_eq_twoCopyLinearFormsProduct
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_mul_sq_le_majorized
import Theorems.Thm_Wikipedia_SzemeredisTheorem_simplexTwoCopyCenteredCorrelation_eq_projected
import Theorems.Thm_Wikipedia_SzemeredisTheorem_simplexTwoCopyMaskedMajorizedCutSystem_form
import Theorems.Thm_Wikipedia_SzemeredisTheorem_simplexTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate

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
# Elementary properties of the linear-forms condition

This file records the normalization and positivity facts that every later
transference estimate uses.  The deep input—that the W-tricked Selberg
majorant satisfies this condition—is isolated in the sieve layer.
-/

namespace Wikipedia.SzemeredisTheorem



@[simp]
theorem linearFormsProduct_empty (k N : ℕ) (ν : ZMod N → ℝ)
    (x : CubePoint k N) :
    linearFormsProduct k N ν (emptyLinearFormsExponent k) x = 1 := by
  simp [linearFormsProduct, emptyLinearFormsExponent]





/-- Testing the empty subproduct forces the error tolerance to be
nonnegative. -/
theorem HasLinearFormsCondition.error_nonneg {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η) :
    0 ≤ η := by
  have he := h (emptyLinearFormsExponent k)
  have hproduct :
      linearFormsProduct k N ν (emptyLinearFormsExponent k) =
        fun _ => 1 := by
    funext x
    exact linearFormsProduct_empty k N ν x
  rw [hproduct] at he
  simpa using he





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









end MajorizedCutSystem

/-! ## Linear-forms certificates for every paid moment -/



namespace MajorizedCutSystem



















/-- Quantitative weighted strong-linear-forms Cauchy--Schwarz bridge.

For a system with `n` remaining coordinates, arbitrary nonnegative cut
factors may be used as long as they are dominated by the certified
majorants.  Repeated Cauchy--Schwarz then costs
`(1 + η)^(2^n - 1)` and terminates at the exact weighted endpoint already
proved in `WeightedStrongLinearForms`. -/
theorem abs_form_pow_two_le_of_hasCFZCertificate
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k)
    {P : Type u} [Fintype P] {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (hS : HasCFZCertificate ν j S) :
    |S.form| ^ (2 ^ n) ≤
      (1 + η) ^ (2 ^ n - 1) *
        ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) := by
  exact abs_form_pow_two_le
    (B := 1 + η)
    (E := (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η)
    (by linarith [hLF.error_nonneg])
    S
    (hasRecursiveBounds_of_hasCFZCertificate hLF j S hS)

/-- Root-extracted form of the weighted strong-linear-forms estimate.

This is the interface used by relative counting: it keeps the analytic
parameter conversion separate from the Cauchy--Schwarz recursion. -/
theorem abs_form_le_of_hasCFZCertificate
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    {G : Type u} [Fintype G] (j : Fin k)
    {P : Type u} [Fintype P] {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (hS : HasCFZCertificate ν j S)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ n - 1) *
          ((2 : ℝ) ^ Fintype.card (DeletedCube k j) * η) ≤
        ε ^ (2 ^ n)) :
    |S.form| ≤ ε := by
  exact le_of_pow_le_pow_left₀
    (pow_ne_zero _ two_ne_zero) hε
    ((abs_form_pow_two_le_of_hasCFZCertificate hLF j S hS).trans hconvert)





end MajorizedCutSystem

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Heterogeneous AP-simplex densification states

The one-colour calculation in `RelativeDensification` uses one common
function on every non-distinguished AP face.  This file performs the same
calculation for a family of face weights `g i`.  For a chosen colour `j`,
the product of all other colours is averaged over the missing `j`
coordinate, then truncated at one on the actual deleted-face space
`Fin n → ZMod N`.

The final section packages the full simplex count and the resulting
lower-arity pairing as two different constructors of one payload type.  In
particular, the projected state is not falsely identified with another
`(n + 1)`-colour AP simplex.  It records the bounded surrogate on its real
domain and separately transports all untouched pointwise majorant bounds
along `j.succAbove`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Heterogeneous AP face systems -/





@[simp]
theorem apHeterogeneousSimplexSystem_edge
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (i : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => ZMod N) i) :
    (apHeterogeneousSimplexSystem n N g).edgeWeight i x =
      g i (apSimplexForm (n + 1) N i x) :=
  rfl



















/-! ## Projection bounds -/













/-! ## Exact heterogeneous count and pairing -/













/-! ## A concrete full-to-projected state transition -/































namespace RelativeDensificationIteration



end RelativeDensificationIteration











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











theorem apMaskedProjectedMajorant_nonneg
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (y : Fin n → ZMod N) :
    0 ≤ apMaskedProjectedMajorant n N ν active j y := by
  unfold apMaskedProjectedMajorant
  exact mean_nonneg fun a =>
    Finset.prod_nonneg fun t _ => by
      cases hactive : active (j.succAbove t) <;>
        simp [apMaskedFaceMajorant, hactive, hν]

/-! ## Masked CFZ selectors -/









/-! ## Exact mixed projected moments -/





/-! ## The recursive moment and state-transition certificates -/

/-- One common CFZ linear-forms condition supplies projected moments for
every choice of active sparse colours.  Inactive colours contribute one and
therefore simply disappear from the selected CFZ subproduct. -/
theorem HasLinearFormsCondition.hasProjectedMajorantMoments_apMaskedProjection
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    HasProjectedMajorantMoments
      (apMaskedProjectedMajorant n N ν active j) η := by
  refine
    { error_nonneg := hLF.error_nonneg
      nonneg := apMaskedProjectedMajorant_nonneg hν active j
      firstMoment_close := ?_
      secondMoment_close := ?_ }
  · rw [mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct]
    exact hLF (apMaskedProjectedOneCopyExponent n active j)
  · rw [mean_apMaskedProjectedMajorant_sq_eq_twoCopyLinearFormsProduct]
    exact hLF (apMaskedProjectedTwoCopyExponent n active j)



end Wikipedia.SzemeredisTheorem

end

section


/-!
# A relative densification step for arbitrary simplex edge functions

The AP-specific transition works with edge functions pulled back from one
function on `ZMod N`.  After re-embedding a projected pairing, however, the
only nonconstant edge is an arbitrary function on its whole deleted-face
space.  This file formulates projection and truncation directly for a
`WeightedSimplexSystem`.

For a fully bounded system the constant-one simplex is a pointwise
majorant.  Its projected majorant is identically one, so its first and
second moment errors are exactly zero.  The resulting generic transition
therefore has zero loss.  In particular it consumes the selectable endpoint
constructed in `RecursiveRelativeCount`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projection of an arbitrary weighted simplex -/















/-! ## Pointwise bounds and projected domination -/















/-! ## The generic analytic transition -/



/-! ## The constant-one majorant -/





@[simp]
theorem generalSimplexIncidentProduct_one
    {G : Type*} {n : ℕ}
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct
      (oneWeightedSimplexSystem G n) j a y = 1 := by
  simp [generalSimplexIncidentProduct,
    oneWeightedSimplexSystem]

@[simp]
theorem generalSimplexProjectedWeight_one
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (j : Fin (n + 1)) :
    generalSimplexProjectedWeight
      (oneWeightedSimplexSystem G n) j =
        fun _ => 1 := by
  funext y
  simp [generalSimplexProjectedWeight]







/-! ## Generic full and projected states -/

























/-! ## Consuming the recursive selectable endpoint -/















end Wikipedia.SzemeredisTheorem

end

section


/-!
# Active-majorant recurrence for relative simplex counting

The weighted Cauchy--Schwarz decoder supplies a certificate when both
copies of every active incident face use the same AP majorant.  Relative
counting also produces two cross terms: one omitted-coordinate copy is
sparse and the other is bounded by one.  This file separates those two
issues exactly.

First, the completed homogeneous certificate is transported from AP
pullback factors to arbitrary weighted-simplex edge factors.  This is
possible because a `HasCFZCertificate` depends on the core and designated
majorants, but not on the particular nonnegative factors below them.

The second part packages the active-cardinality bookkeeping and the
one-step counting recurrence.  Its only extra strong-linear-forms input is
the pair of genuinely mixed-copy centered correlations.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Factor-independence of structural CFZ certificates -/

namespace MajorizedCutSystem



end MajorizedCutSystem

/-! ## Arbitrary simplex factors under homogeneous AP majorants -/



















/-- Quantitative homogeneous-mask strong-linear-forms bound for arbitrary
weighted-simplex edge factors. -/
theorem HasLinearFormsCondition.abs_simplexTwoCopyCenteredCorrelation_le_of_masked
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apMaskedFaceMajorant ν active)).edgeWeight
                (j.succAbove t) x)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν H j| ≤ ε := by
  rw [← simplexTwoCopyMaskedMajorizedCutSystem_form
    (m + 1) N ν active H j hrest]
  exact
    MajorizedCutSystem.abs_form_le_of_hasCFZCertificate
      hLF j
      (simplexTwoCopyMaskedMajorizedCutSystem
        (m + 1) N ν active H j hrest)
      (simplexTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
        (m + 1) N ν hν active H j hrest)
      hε hconvert

/-! ## Active-face cardinality and the comparison invariant -/























/-! ## Replacing one canonical edge by a whole-face function -/



























/-! ## The exact mixed-copy strong-linear-forms interface -/













/-- Homogeneous sparse-copy correlation, specialized from the arbitrary
factor terminal decoder. -/
theorem HasLinearFormsCondition.abs_simplexTwoCopyCenteredCorrelation_le_of_majorized
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem
          (m + 1) N ν active))
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => H) j| ≤ ε := by
  exact
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_masked
      hν active (fun _ => H) j
      (fun _b t x => hH (j.succAbove t) x)
      hε hconvert

/-- Homogeneous dense-copy correlation.  The common decoder mask is empty,
so every designated incident majorant is one. -/
theorem HasLinearFormsCondition.abs_simplexTwoCopyCenteredCorrelation_le_of_unit
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hK : EdgeWeightsInUnitInterval K)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => K) j| ≤ ε := by
  apply
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_masked
      hν (fun _ => false) (fun _ => K) j
      _ hε hconvert
  intro _b t x
  refine ⟨(hK (j.succAbove t) x).1, ?_⟩
  simpa [apMaskedFaceMajorant] using
    (hK (j.succAbove t) x).2

/-- The same empty-mask correlation with all incident factors one bounds
the mean of the centered distinguished AP face. -/
theorem HasLinearFormsCondition.abs_mean_apFaceCenteredCore_le
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (m + 2))
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |mean (apFaceCenteredCore (m + 1) N ν j)| ≤ ε := by
  have h :=
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_unit
      hν
      (oneWeightedSimplexSystem (ZMod N) (m + 1))
      j
      (fun _ _ => ⟨zero_le_one, le_rfl⟩)
      hε hconvert
  rw [simplexTwoCopyCenteredCorrelation_eq_projected] at h
  simpa using h



/-! ## Direct cut term and projected pointwise bounds -/















/-! ## Truncation and the lower-cardinality quadratic term -/







/-! ## One active-face recurrence -/











end Wikipedia.SzemeredisTheorem

end
/-!
# Active-majorant recurrence for relative simplex counting

The weighted Cauchy--Schwarz decoder supplies a certificate when both
copies of every active incident face use the same AP majorant.  Relative
counting also produces two cross terms: one omitted-coordinate copy is
sparse and the other is bounded by one.  This file separates those two
issues exactly.

First, the completed homogeneous certificate is transported from AP
pullback factors to arbitrary weighted-simplex edge factors.  This is
possible because a `HasCFZCertificate` depends on the core and designated
majorants, but not on the particular nonnegative factors below them.

The second part packages the active-cardinality bookkeeping and the
one-step counting recurrence.  Its only extra strong-linear-forms input is
the pair of genuinely mixed-copy centered correlations.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Factor-independence of structural CFZ certificates -/
/-! ## Arbitrary simplex factors under homogeneous AP majorants -/
/-! ## Active-face cardinality and the comparison invariant -/
/-! ## Replacing one canonical edge by a whole-face function -/
/-! ## The exact mixed-copy strong-linear-forms interface -/
/-! ## Direct cut term and projected pointwise bounds -/
/-! ## Truncation and the lower-cardinality quadratic term -/
/-! ## One active-face recurrence -/

open Wikipedia.SzemeredisTheorem.HasLinearFormsCondition in
/-- Weighted Cauchy--Schwarz controls the projection-difference term in one
active-face replacement.

The homogeneous sparse/sparse and dense/dense correlations, as well as the
mean of the distinguished AP majorant, come from the completed common-mask
decoder.  `HasActiveFaceCrossCorrelationLe` supplies exactly the two
heterogeneous cross terms. -/
theorem solution
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    {active : Fin (m + 2) → Bool}
    {cutError countError ξ σ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (m + 2))
    (hj : active j = true)
    (hlower :
      MaskedSimplexComparisonLe (m + 1) N ν
        (deactivateFace active j) cutError countError)
    (hcross :
      HasActiveFaceCrossCorrelationLe
        (m + 1) N ν active j ξ)
    (hξ : 0 ≤ ξ)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ξ ^ (2 ^ (m + 1)))
    (hσ : 0 ≤ σ)
    (hroot :
      (1 + ξ) *
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError + 4 * ξ) ≤
        σ ^ 2)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem
          (m + 1) N ν active))
    (hK : EdgeWeightsInUnitInterval K)
    (hcut : EdgeFaceCutDiscrepancyLe H K cutError) :
    |mean (fun y =>
        generalSimplexDistinguishedWeight H j y *
          (generalSimplexProjectedWeight H j y -
            generalSimplexProjectedWeight K j y))| ≤
      σ := by
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  let u := generalSimplexDistinguishedWeight H j
  let v : (Fin (m + 1) → ZMod N) → ℝ :=
    fun y =>
      ν (apSimplexForm (m + 2) N j
        (finTupleToDeletedVector j y))
  let c := apFaceCenteredCore (m + 1) N ν j
  have hMoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight
          (apMaskedSimplexMajorantSystem
            (m + 1) N ν active) j) η := by
    change
      HasProjectedMajorantMoments
        (apMaskedProjectedMajorant
          (m + 1) N ν active j) η
    exact
      hLF.hasProjectedMajorantMoments_apMaskedProjection
        hν active j
  have hL2 :
      mean (fun y => (A y - B y) ^ 2) ≤
        3 * η + 2 * Real.sqrt (3 * η) +
          2 * countError := by
    exact
      hMoments.mean_projectedDifference_sq_le
        j hlower hH hK hcut
  have hHH :
      |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => H) j| ≤ ξ :=
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_majorized
      hν active H j hH hξ hconvert
  have hKK :
      |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => K) j| ≤ ξ :=
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_unit
      hν K j hK hξ hconvert
  have hcentered :
      |mean (fun y =>
          c y * (A y - B y) ^ 2)| ≤
        4 * ξ := by
    exact
      abs_centered_projectedDifference_sq_le
        (m + 1) N ν H K j hHH hKK
        (hcross H K hH hK)
  have hcore :
      |mean c| ≤ ξ :=
    hLF.abs_mean_apFaceCenteredCore_le
      hν j hξ hconvert
  have hv0 : ∀ y, 0 ≤ v y :=
    fun y => hν _
  have hu0 : ∀ y, 0 ≤ u y := by
    intro y
    exact (hH j (finTupleToDeletedVector j y)).1
  have huv : ∀ y, u y ≤ v y := by
    intro y
    have hupper :=
      (hH j (finTupleToDeletedVector j y)).2
    simpa [u, v, generalSimplexDistinguishedWeight,
      apMaskedSimplexMajorantSystem,
      apMaskedFaceMajorant, hj] using hupper
  have hvc : ∀ y, v y = c y + 1 := by
    intro y
    simp [v, c, apFaceCenteredCore]
  have hmeanV :
      mean v ≤ 1 + ξ := by
    have hrewrite :
        mean v = mean c + 1 := by
      calc
        mean v = mean (fun y => c y + 1) := by
          apply congrArg mean
          funext y
          exact hvc y
        _ = mean c + mean (fun _ => (1 : ℝ)) :=
          mean_add _ _
        _ = mean c + 1 := by rw [mean_const]
    rw [hrewrite]
    linarith [le_abs_self (mean c), hcore]
  have hweighted0 :
      0 ≤ mean (fun y =>
        v y * (A y - B y) ^ 2) :=
    mean_nonneg fun y =>
      mul_nonneg (hv0 y) (sq_nonneg _)
  have hweighted :
      mean (fun y =>
          v y * (A y - B y) ^ 2) ≤
        3 * η + 2 * Real.sqrt (3 * η) +
          2 * countError + 4 * ξ := by
    have hrewrite :
        mean (fun y =>
            v y * (A y - B y) ^ 2) =
          mean (fun y => (A y - B y) ^ 2) +
          mean (fun y =>
            c y * (A y - B y) ^ 2) := by
      rw [← mean_add]
      apply congrArg mean
      funext y
      rw [hvc y]
      ring
    rw [hrewrite]
    calc
      mean (fun y => (A y - B y) ^ 2) +
          mean (fun y =>
            c y * (A y - B y) ^ 2) ≤
          mean (fun y => (A y - B y) ^ 2) +
            |mean (fun y =>
              c y * (A y - B y) ^ 2)| :=
        add_le_add le_rfl (le_abs_self _)
      _ ≤
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError) + 4 * ξ :=
        add_le_add hL2 hcentered
      _ =
          3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError + 4 * ξ := by ring
  have hcs :
      mean (fun y => u y * (A y - B y)) ^ 2 ≤
        mean v *
          mean (fun y =>
            v y * (A y - B y) ^ 2) :=
    mean_mul_sq_le_majorized u v
      (fun y => A y - B y) hu0 huv
  have hproduct :
      mean v *
          mean (fun y =>
            v y * (A y - B y) ^ 2) ≤
        (1 + ξ) *
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError + 4 * ξ) := by
    exact
      mul_le_mul hmeanV hweighted hweighted0
        (by linarith)
  have hsquare :
      |mean (fun y => u y * (A y - B y))| ^ 2 ≤
        σ ^ 2 := by
    rw [sq_abs]
    exact hcs.trans (hproduct.trans hroot)
  exact
    (sq_le_sq₀
      (abs_nonneg
        (mean (fun y => u y * (A y - B y))))
      hσ).mp hsquare
