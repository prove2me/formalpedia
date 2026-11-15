-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.simplexTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:00:31.409905+00:00
-- url     : https://prove2.me/submissions/773c7dc0-d5e6-4e5f-89de-475c71d281b3

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_HasCFZCertificate_of_core_majorant_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MajorizedCutSystem_apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate

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

open Wikipedia.SzemeredisTheorem in
/-- The arbitrary-factor system has the same core and designated
majorants as the already certified AP-pullback system. -/
theorem solution
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apMaskedFaceMajorant ν active)).edgeWeight
                (j.succAbove t) x) :
    MajorizedCutSystem.HasCFZCertificate ν j
      (simplexTwoCopyMaskedMajorizedCutSystem
        n N ν active H j hrest) := by
  let g : Bool → APFaceWeightFamily n N :=
    fun _ => apMaskedFaceMajorant ν active
  have hg :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j := by
    intro b t z
    exact
      ⟨by
        cases hactive : active (j.succAbove t) <;>
          simp [g, hactive, hν],
        le_rfl⟩
  let T :=
    apTwoCopyMaskedMajorizedCutSystem
      n N ν active g j hg
  apply MajorizedCutSystem.HasCFZCertificate.of_core_majorant_eq
      j (S :=
        simplexTwoCopyMaskedMajorizedCutSystem
          n N ν active H j hrest) (T := T)
  · intro a y
    rfl
  · intro a t z
    rfl
  · exact
      MajorizedCutSystem.apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
        n N ν active g j hg
