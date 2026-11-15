-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.maskedSimplexComparisonLe_of_activeFaceInduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:05:23.0422+00:00
-- url     : https://prove2.me/submissions/cacb750a-8594-4c85-ab14-b2e6c6a3f726

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_maskedSimplexComparisonLe_step
import Theorems.Thm_Wikipedia_SzemeredisTheorem_activeFaceCount_eq_zero_iff
import Theorems.Thm_Wikipedia_SzemeredisTheorem_maskedSimplexComparisonLe_of_inactive

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





















/-! ## Active-face cardinality and the comparison invariant -/





@[simp]
theorem mem_activeFaceSet
    {k : ℕ} (active : Fin k → Bool) (i : Fin k) :
    i ∈ activeFaceSet active ↔ active i = true := by
  simp [activeFaceSet]

/-- Deactivation erases exactly the selected active face. -/
theorem activeFaceSet_deactivateFace
    {k : ℕ} (active : Fin k → Bool) (j : Fin k) :
    activeFaceSet (deactivateFace active j) =
      (activeFaceSet active).erase j := by
  ext i
  by_cases hij : i = j
  · subst i
    simp [deactivateFace]
  · simp [deactivateFace, hij]

/-- Deactivating an active face lowers the active count by one. -/
theorem activeFaceCount_deactivateFace
    {k : ℕ} (active : Fin k → Bool) (j : Fin k)
    (hj : active j = true) :
    activeFaceCount (deactivateFace active j) + 1 =
      activeFaceCount active := by
  unfold activeFaceCount
  rw [activeFaceSet_deactivateFace]
  exact Finset.card_erase_add_one
    (mem_activeFaceSet active j |>.2 hj)











/-- Cardinality-zero form of the bounded induction base. -/
theorem maskedSimplexComparisonLe_of_activeFaceCount_zero
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (hactive : activeFaceCount active = 0)
    (cutError : ℝ) :
    MaskedSimplexComparisonLe n N ν active
      cutError (((n + 1 : ℕ) : ℝ) * cutError) :=
  maskedSimplexComparisonLe_of_inactive
    n N ν active
    ((activeFaceCount_eq_zero_iff active).1 hactive)
    cutError

/-! ## Replacing one canonical edge by a whole-face function -/



























/-! ## The exact mixed-copy strong-linear-forms interface -/





















/-! ## Direct cut term and projected pointwise bounds -/















/-! ## Truncation and the lower-cardinality quadratic term -/







/-! ## One active-face recurrence -/





/-- A proved comparison remains valid after enlarging its count-error
budget. -/
theorem MaskedSimplexComparisonLe.mono_countError
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {cutError countError countError' : ℝ}
    (h :
      MaskedSimplexComparisonLe n N ν active
        cutError countError)
    (hle : countError ≤ countError') :
    MaskedSimplexComparisonLe n N ν active
      cutError countError' := by
  intro H K hH hK hcut
  exact (h H K hH hK hcut).trans hle





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
/-- Strong induction on the number of active faces.

`error r` is the count-error budget after `r` sparse faces remain.  The
base hypothesis absorbs the bounded telescoping estimate, while
`hroot` is exactly the numerical recurrence generated by weighted
Cauchy--Schwarz.  The only structural hypothesis not discharged in this
file is `hcross`, the copy-dependent two-orientation correlation bound. -/
theorem solution
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    {cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (error : ℕ → ℝ)
    (hbase :
      (((m + 2 : ℕ) : ℝ) * cutError) ≤ error 0)
    (hcross :
      ∀ (active : Fin (m + 2) → Bool)
        (j : Fin (m + 2)),
        active j = true →
        HasActiveFaceCrossCorrelationLe
          (m + 1) N ν active j ξ)
    (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1)))
    (hnext :
      ∀ r : ℕ, cutError ≤ error (r + 1))
    (hroot :
      ∀ r : ℕ,
        (1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * error r + 4 * ξ) ≤
          (error (r + 1) - cutError) ^ 2)
    (active : Fin (m + 2) → Bool) :
    MaskedSimplexComparisonLe (m + 1) N ν active
      cutError (error (activeFaceCount active)) := by
  classical
  let P : ℕ → Prop := fun s =>
    ∀ active : Fin (m + 2) → Bool,
      activeFaceCount active = s →
      MaskedSimplexComparisonLe (m + 1) N ν active
        cutError (error s)
  have hP : ∀ s, P s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        change
          ∀ active : Fin (m + 2) → Bool,
            activeFaceCount active = s →
            MaskedSimplexComparisonLe (m + 1) N ν active
              cutError (error s)
        intro active hcard
        by_cases hs : s = 0
        · have hzero : activeFaceCount active = 0 :=
            hcard.trans hs
          have hbaseComparison :=
            (maskedSimplexComparisonLe_of_activeFaceCount_zero
              (m + 1) N ν active hzero cutError).mono_countError
                hbase
          simpa [hs] using hbaseComparison
        · have hspos : 0 < s := Nat.pos_of_ne_zero hs
          have hsetNonempty :
              (activeFaceSet active).Nonempty := by
            exact Finset.card_pos.mp (by
              change 0 < activeFaceCount active
              rw [hcard]
              exact hspos)
          obtain ⟨j, hjset⟩ := hsetNonempty
          have hj : active j = true :=
            (mem_activeFaceSet active j).1 hjset
          let r :=
            activeFaceCount (deactivateFace active j)
          have hradd :
              r + 1 = activeFaceCount active := by
            exact activeFaceCount_deactivateFace active j hj
          have hrs : r + 1 = s := by
            rw [hradd, hcard]
          have hrlt : r < s := by omega
          have hlower :
              MaskedSimplexComparisonLe (m + 1) N ν
                (deactivateFace active j) cutError (error r) := by
            exact
              ih r hrlt (deactivateFace active j) rfl
          have hstep :
              MaskedSimplexComparisonLe (m + 1) N ν active
                cutError
                ((error (r + 1) - cutError) + cutError) := by
            exact
              hLF.maskedSimplexComparisonLe_step
                hν j hj hlower (hcross active j hj)
                hξ (hconvert j)
                (sub_nonneg.mpr (hnext r))
                (hroot r)
          have herr :
              (error (r + 1) - cutError) + cutError =
                error s := by
            rw [hrs]
            ring
          rw [← herr]
          exact hstep
  exact hP (activeFaceCount active) active rfl
