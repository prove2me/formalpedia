-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.simplexTwoCopyMaskedMajorizedCutSystem_form
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:43:16.456195+00:00
-- url     : https://prove2.me/submissions/19cec576-6fc1-4bc7-ba35-aa450ed8bebf

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



/-- Evaluation on an erased shared tuple recovers the two actual incident
edge factors. -/
theorem simplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (y : Fin n → ZMod N) :
    simplexTwoCopyCutTest n N H j a t
        (eraseCoordinate t y) =
      ∏ b : Bool,
        (H b).edgeWeight (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j (a b) y)
            (j.succAbove t)) := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      unfold simplexTwoCopyCutTest
      apply Fintype.prod_congr
      intro b
      rw [insertNth_insertNth_eraseCoordinate]
      rw [deleteCoordinate_update_same]

/-- Products of the reconstructed factors are the two incident simplex
products. -/
theorem prod_simplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → ZMod N) :
    (∏ t : Fin n,
        simplexTwoCopyCutTest n N H j a t
          (eraseCoordinate t y)) =
      ∏ b : Bool,
        generalSimplexIncidentProduct (H b) j (a b) y := by
  simp_rw [simplexTwoCopyCutTest_eraseCoordinate]
  unfold generalSimplexIncidentProduct
  rw [Finset.prod_comm]















/-! ## Active-face cardinality and the comparison invariant -/























/-! ## Replacing one canonical edge by a whole-face function -/



























/-! ## The exact mixed-copy strong-linear-forms interface -/





















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

open Wikipedia.SzemeredisTheorem in
/-- The arbitrary-factor system represents its centered projected
correlation exactly. -/
theorem solution
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
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
    (simplexTwoCopyMaskedMajorizedCutSystem
        n N ν active H j hrest).form =
      simplexTwoCopyCenteredCorrelation n N ν H j := by
  unfold MajorizedCutSystem.form
  unfold simplexTwoCopyMaskedMajorizedCutSystem
  unfold simplexTwoCopyCenteredCorrelation
  apply congrArg mean
  funext a
  apply congrArg mean
  funext y
  change
    apFaceCenteredCore n N ν j y *
        ∏ t : Fin n,
          simplexTwoCopyCutTest n N H j a t
            (eraseCoordinate t y) =
      apFaceCenteredCore n N ν j y *
        ∏ b : Bool,
          generalSimplexIncidentProduct (H b) j (a b) y
  rw [prod_simplexTwoCopyCutTest_eraseCoordinate]
