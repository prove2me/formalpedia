-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:15:19.719593+00:00
-- url     : https://prove2.me/theorems/b5547a92-8384-4540-9f32-4ca3f442fe7e
-- title:
--   Active-face comparison interfaces for relative simplex counting
-- statement:
--   For weighted simplex systems over $\mathbb Z/N\mathbb Z$, this bundle reconstructs two-copy cut tests, centered correlations, and the common-mask majorized cut system. An active-face set and its cardinality record which majorants remain sparse. Pointwise majorization requires every edge weight to be nonnegative and below the corresponding masked AP majorant.
--
--   For $N
--   e0$, the masked comparison predicate states that any such sparse system and any unit-bounded dense system with edge-face cut discrepancy at most $c$ have simplex counts differing by at most $e$. Edge replacement and Boolean pairing constructions support the induction. The sparse-dense cross-correlation predicate bounds both orientations; its mask-level version quantifies over all sparse and dense systems satisfying the stated domination bounds. An incident-cut construction freezes the omitted vertex of one simplex system.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingInduction.lean#L100-L1201

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
import Lean
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

/-- Reconstruct the `t`-th two-copy cut factor from arbitrary weighted
simplex systems.  The inserted zero is irrelevant because the edge of
colour `j.succAbove t` omits exactly that coordinate. -/
def simplexTwoCopyCutTest
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N) :
    CutTestFamily (ZMod N) n := by
  cases n with
  | zero =>
      exact fun t => Fin.elim0 t
  | succ m =>
      exact fun t z =>
        ∏ b : Bool,
          (H b).edgeWeight (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (a b)
                (Fin.insertNth t 0 z))
              (j.succAbove t))





/-- Pointwise domination of arbitrary simplex edges gives domination of
their reconstructed two-copy cut factors. -/
theorem simplexTwoCopyCutTest_mono
    (n N : ℕ)
    (H K : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hHK :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (K b).edgeWeight (j.succAbove t) x)
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    0 ≤ simplexTwoCopyCutTest n N H j a t z ∧
      simplexTwoCopyCutTest n N H j a t z ≤
        simplexTwoCopyCutTest n N K j a t z := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      constructor
      · unfold simplexTwoCopyCutTest
        exact Finset.prod_nonneg fun b _ => (hHK b t _).1
      · unfold simplexTwoCopyCutTest
        exact Finset.prod_le_prod
          (fun b _ => (hHK b t _).1)
          (fun b _ => (hHK b t _).2)

/-- The generic reconstructed cut factor specializes to the existing AP
pullback factor. -/
theorem simplexTwoCopyCutTest_apHeterogeneous
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    simplexTwoCopyCutTest n N
        (fun b => apHeterogeneousSimplexSystem n N (g b))
        j a t z =
      apTwoCopyCutTest n N g j a t z := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => rfl

/-- Centered two-copy projected correlation for arbitrary weighted
simplex systems. -/
noncomputable def simplexTwoCopyCenteredCorrelation
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1)) : ℝ :=
  mean₂ fun a : Bool → ZMod N => fun y : Fin n → ZMod N =>
    apFaceCenteredCore n N ν j y *
      ∏ b : Bool,
        generalSimplexIncidentProduct (H b) j (a b) y

/-- The arbitrary-factor system used for a common active mask. -/
noncomputable def simplexTwoCopyMaskedMajorizedCutSystem
    (n N : ℕ)
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
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a => simplexTwoCopyCutTest n N H j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (fun _ => apMaskedFaceMajorant ν active) j a
  factor_nonneg := by
    intro a t z
    have hmono :=
      simplexTwoCopyCutTest_mono n N H
        (fun _ =>
          apHeterogeneousSimplexSystem n N
            (apMaskedFaceMajorant ν active))
        j hrest a t z
    exact hmono.1
  factor_le_majorant := by
    intro a t z
    have hmono :=
      simplexTwoCopyCutTest_mono n N H
        (fun _ =>
          apHeterogeneousSimplexSystem n N
            (apMaskedFaceMajorant ν active))
        j hrest a t z
    change
      simplexTwoCopyCutTest n N H j a t z ≤
        apTwoCopyCutTest n N
          (fun _ => apMaskedFaceMajorant ν active) j a t z
    rw [← simplexTwoCopyCutTest_apHeterogeneous
      n N (fun _ => apMaskedFaceMajorant ν active)
      j a t z]
    exact hmono.2







/-! ## Active-face cardinality and the comparison invariant -/

/-- The finite set of faces whose designated majorant is still `ν`. -/
def activeFaceSet
    {k : ℕ} (active : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => active i = true

/-- Number of still-sparse face majorants. -/
def activeFaceCount
    {k : ℕ} (active : Fin k → Bool) : ℕ :=
  (activeFaceSet active).card









/-- Pointwise nonnegative domination of every edge of one simplex system
by the corresponding edge of another. -/
def SimplexEdgeMajorizedBy
    {G : Type*} {n : ℕ}
    (H M : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) : Prop :=
  ∀ i x,
    0 ≤ H.edgeWeight i x ∧
      H.edgeWeight i x ≤ M.edgeWeight i x

/-- The AP simplex system carrying the Boolean-mask majorants. -/
def apMaskedSimplexMajorantSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N) :=
  apHeterogeneousSimplexSystem n N
    (apMaskedFaceMajorant ν active)

/-- Relative counting for arbitrary simplex edge functions under the
canonical AP mask.

Allowing arbitrary edge functions is essential: inserting a lower-face cut
into one edge is how the induction proves projected face-cut discrepancy. -/
def MaskedSimplexComparisonLe
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (cutError countError : ℝ) : Prop :=
  ∀ (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)),
    SimplexEdgeMajorizedBy H
      (apMaskedSimplexMajorantSystem n N ν active) →
    EdgeWeightsInUnitInterval K →
    EdgeFaceCutDiscrepancyLe H K cutError →
    |H.simplexCount - K.simplexCount| ≤ countError





/-! ## Replacing one canonical edge by a whole-face function -/

/-- Replace the selected edge by an arbitrary function in canonical
`Fin n` face coordinates. -/
noncomputable def setSimplexEdge
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G) where
  edgeWeight i x :=
    if hij : i = j then
      f (deletedFaceTuple j (hij ▸ x))
    else H.edgeWeight i x

























/-! ## The exact mixed-copy strong-linear-forms interface -/

/-- A Boolean pair of simplex systems, with `H` in the false copy and `K`
in the true copy. -/
def simplexCopyPair
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => G)
  | false => H
  | true => K





/-- The two genuinely mixed-copy centered correlations required by one
active-majorant recurrence step.

The homogeneous `H,H` and `K,K` correlations are already consequences of
the terminal decoder.  Only these two orientations require independent
majorant masks on the two initial Boolean copies. -/
def HasSparseDenseCrossCorrelationLe
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (ε : ℝ) : Prop :=
  |simplexTwoCopyCenteredCorrelation n N ν
      (simplexCopyPair H K) j| ≤ ε ∧
  |simplexTwoCopyCenteredCorrelation n N ν
      (simplexCopyPair K H) j| ≤ ε

/-- Mask-level form of the only heterogeneous strong-linear-forms input
needed by an induction step.

It quantifies over the arbitrary sparse and dense simplex systems appearing
in `MaskedSimplexComparisonLe`.  A copy-dependent CFZ certificate can
discharge this interface directly: the false and true Boolean copies use
the active AP mask and the constant-one mask, respectively, and the second
conjunct swaps those two masks. -/
def HasActiveFaceCrossCorrelationLe
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (ε : ℝ) : Prop :=
  ∀ (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)),
    SimplexEdgeMajorizedBy H
      (apMaskedSimplexMajorantSystem n N ν active) →
    EdgeWeightsInUnitInterval K →
    HasSparseDenseCrossCorrelationLe n N ν H K j ε











/-! ## Direct cut term and projected pointwise bounds -/

/-- The incident product of one fixed simplex system, reconstructed as a
cut-test family after fixing the omitted vertex. -/
def simplexIncidentCutTest
    {G : Type*} {n : ℕ}
    (K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G) :
    CutTestFamily G n :=
  fun t z =>
    K.edgeWeight (j.succAbove t)
      (deleteCoordinate
        (Fin.insertNth j a
          (insertErasedCoordinate t a z))
        (j.succAbove t))













/-! ## Truncation and the lower-cardinality quadratic term -/







/-! ## One active-face recurrence -/











end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.HasSparseDenseCrossCorrelationLe.eq_1,
    `Wikipedia.SzemeredisTheorem.MaskedSimplexComparisonLe.congr_simp,
    `Wikipedia.SzemeredisTheorem.SimplexEdgeMajorizedBy.eq_1,
    `Wikipedia.SzemeredisTheorem.activeFaceSet.eq_1,
    `Wikipedia.SzemeredisTheorem.apMaskedSimplexMajorantSystem.eq_1,
    `Wikipedia.SzemeredisTheorem.setSimplexEdge.eq_1,
    `Wikipedia.SzemeredisTheorem.simplexCopyPair.eq_1,
    `Wikipedia.SzemeredisTheorem.simplexCopyPair.eq_2,
    `Wikipedia.SzemeredisTheorem.simplexCopyPair.match_1,
    `Wikipedia.SzemeredisTheorem.simplexIncidentCutTest.eq_1,
    `Wikipedia.SzemeredisTheorem.simplexTwoCopyCenteredCorrelation.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


