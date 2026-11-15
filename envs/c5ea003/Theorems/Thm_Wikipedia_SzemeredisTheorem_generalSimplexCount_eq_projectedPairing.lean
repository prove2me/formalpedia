-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_generalSimplexCount_eq_projectedPairing
-- name    : Wikipedia.SzemeredisTheorem.generalSimplexCount_eq_projectedPairing
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:07:55.343132+00:00
-- url     : https://prove2.me/theorems/523f389d-6ee1-4f0d-a908-3cd4d2dac480
-- title:
--   A simplex count is a pairing of projected and distinguished weights
-- statement:
--   For a finite type $G$, a weighted simplex system $H$ on $n+1$ copies of $G$, and any distinguished face $j$, its normalized simplex count equals the mean of the product of its projected weight and distinguished weight at $j$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/GeneralRelativeSimplexStep.lean#L98-L135

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Projection of an arbitrary weighted simplex -/

theorem Wikipedia.SzemeredisTheorem.generalSimplexCount_eq_projectedPairing
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    H.simplexCount =
      mean (fun y =>
        generalSimplexProjectedWeight H j y *
          generalSimplexDistinguishedWeight H j y) := by sorry
