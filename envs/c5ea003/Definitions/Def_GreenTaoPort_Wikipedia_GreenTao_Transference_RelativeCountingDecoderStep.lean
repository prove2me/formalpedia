-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderStep
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderStep
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:09:42.232069+00:00
-- url     : https://prove2.me/theorems/083cbfa5-a42f-4720-97d6-9522c1b2deee
-- title:
--   Ordered stage coordinates for the Cauchy–Schwarz decoder
-- statement:
--   For a Cauchy–Schwarz stage with $r$ processed coordinates and $s$ future coordinates, this bundle defines the current original index, reconstructs the original cut-factor input, and transports between the recursive arity $(s+1)+r$ and geometric order $r+(s+1)$. The tuple prefix operator concatenates the $r$ processed values with the $s$ future values; when $r=0$, it returns the future tuple. The ordered cube equivalence splits the full AP cube into its stage parameter and live tail, together with unused endpoint fibers.
--
--   For a distinguished face $j$, the current paid face is obtained by skipping $j$ at the current deleted-coordinate index. Boolean choices determine its generated vertices: the distinguished coordinate and processed coordinates vary, while future coordinates are fixed to false. An explicit equivalence identifies these choices with their image. The ordered stage exponent selects exactly those generated vertices when the paid face is active.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingDecoderStep.lean#L19-L1190

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoder
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
# Pointwise stage identities for relative counting

This file turns the stage equivalence from
`RelativeCountingDecoder` into closed formulas for the majorants generated
by repeated `MajorizedCutSystem.next`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Prefixing the processed endpoint choices -/

/-- Put `r` processed coordinate values in front of an `s`-coordinate
future tuple.  The apparently reversed length `s + r` is chosen because it
is definitionally compatible with recursion on `r`. -/
def csPrependTuple
    {G : Type u} {s : ℕ} :
    ∀ r : ℕ,
      (Fin r → G) → (Fin s → G) →
        (Fin (s + r) → G)
  | 0, _a, z => z
  | r + 1, a, z =>
      Fin.cons (a 0)
        (csPrependTuple r (Fin.tail a) z)







/-- Add a head value to a possibly zero-dimensional tuple. -/
def csConsInput
    {G : Type u} :
    ∀ n : ℕ, G → (Fin (n - 1) → G) → Fin n → G
  | 0, _a, _z => fun i => Fin.elim0 i
  | _n + 1, a, z => Fin.cons a z







/-- The original coordinate paid after `r` head coordinates have already
been eliminated. -/
def csOrderedStageCurrentIndex
    (r s : ℕ) :
    Fin ((s + 1) + r) :=
  ⟨r, by omega⟩

/-- Reconstruct the input to the original current-coordinate cut factor
from choices on the processed coordinates and the shared future tuple. -/
def csOrderedStageFactorInput
    {G : Type u} :
    ∀ r s : ℕ,
      (Fin r → G) → (Fin s → G) →
        (Fin (((s + 1) + r) - 1) → G)
  | 0, _s, _a, z => z
  | r + 1, s, a, z =>
      csConsInput ((s + 1) + r) (a 0)
        (csOrderedStageFactorInput r s
          (Fin.tail a) z)















/-! ## Closed formula for an iterated designated majorant -/

namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## The selected stage vertices -/















/-! ## Transport from recursive to geometric coordinate order -/

/-- Equality of the two deleted-coordinate arity expressions. -/
theorem apCSStageDeletedArityEq (r s : ℕ) :
    (s + 1) + r =
      r + (s + 1) := by
  omega

/-- The recursive dimension expression and the geometric prefix expression
have the same value. -/
theorem apCSStageArityEq (r s : ℕ) :
    ((s + 1) + r) + 1 =
      (r + (s + 1)) + 1 :=
  congrArg (fun q => q + 1)
    (apCSStageDeletedArityEq r s)



/-- Transport the distinguished face from the recursive dimension order to
the geometric prefix order used by `apCSStageCubeEquiv`. -/
def apCSStageTransportJ
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    Fin ((r + (s + 1)) + 1) :=
  Fin.cast (apCSStageArityEq r s) j



/-- Transport a full cube point across the arithmetic arity equality. -/
def apCSStageCubeTransportEquiv
    (r s N : ℕ) :
    CubePoint (((s + 1) + r) + 1) N ≃
      CubePoint ((r + (s + 1)) + 1) N :=
  Equiv.arrowCongr
    (finCongr (apCSStageArityEq r s))
    (Equiv.refl (Bool → ZMod N))

/-- The stage decoder with the original recursive arity exposed at its
domain. -/
def apCSOrderedStageCubeEquiv
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    CubePoint (((s + 1) + r) + 1) N ≃
      ((CSStageParam (Bool → ZMod N) (ZMod N) r ×
          (Fin s → ZMod N)) ×
        ((ZMod N × ZMod N) × (Fin s → ZMod N))) :=
  (apCSStageCubeTransportEquiv r s N).trans
    (apCSStageCubeEquiv r s N
      (apCSStageTransportJ r s j))

/-- The `i`-th processed deleted coordinate in recursive arity order. -/
def csOrderedStageProcessedIndex
    (r s : ℕ) (i : Fin r) :
    Fin ((s + 1) + r) :=
  ⟨i, by omega⟩

/-- The `t`-th future deleted coordinate in recursive arity order. -/
def csOrderedStageFutureIndex
    (r s : ℕ) (t : Fin s) :
    Fin ((s + 1) + r) :=
  ⟨r + 1 + t, by omega⟩









/-! ## The same selector in recursive arity order -/

/-- Current face in the original recursive arity order. -/
def apCSOrderedStageCurrentFace
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    Fin (((s + 1) + r) + 1) :=
  j.succAbove (csOrderedStageCurrentIndex r s)

/-- Current-face vertex in recursive arity order. -/
noncomputable def apCSOrderedStageVertex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool) :
    DeletedCube
      (((s + 1) + r) + 1)
      (apCSOrderedStageCurrentFace r s j) :=
  fun i =>
    if hij : i.1 = j then
      bits 0
    else
      let t :=
        (finSuccAboveEquiv j).symm
          ⟨i.1, hij⟩
      if ht : t.val < r then
        bits (Fin.succ ⟨t.val, ht⟩)
      else
        false

def apCSOrderedStageDistinguishedVertexIndex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    {i : Fin (((s + 1) + r) + 1) //
      i ≠ apCSOrderedStageCurrentFace r s j} :=
  ⟨j, (Fin.succAbove_ne j
    (csOrderedStageCurrentIndex r s)).symm⟩

def apCSOrderedStageProcessedVertexIndex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (i : Fin r) :
    {q : Fin (((s + 1) + r) + 1) //
      q ≠ apCSOrderedStageCurrentFace r s j} :=
  ⟨j.succAbove (csOrderedStageProcessedIndex r s i), by
    intro h
    have ht :=
      Fin.succAbove_right_injective (p := j) h
    have hv := congrArg Fin.val ht
    simp [csOrderedStageProcessedIndex,
      csOrderedStageCurrentIndex] at hv
    omega⟩

def apCSOrderedStageFutureVertexIndex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (t : Fin s) :
    {q : Fin (((s + 1) + r) + 1) //
      q ≠ apCSOrderedStageCurrentFace r s j} :=
  ⟨j.succAbove (csOrderedStageFutureIndex r s t), by
    intro h
    have ht :=
      Fin.succAbove_right_injective (p := j) h
    have hv := congrArg Fin.val ht
    simp [csOrderedStageFutureIndex,
      csOrderedStageCurrentIndex] at hv
    omega⟩

@[simp]
theorem apCSOrderedStageVertex_distinguished
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool) :
    apCSOrderedStageVertex r s j bits
        (apCSOrderedStageDistinguishedVertexIndex r s j) =
      bits 0 := by
  simp [apCSOrderedStageVertex,
    apCSOrderedStageDistinguishedVertexIndex]

@[simp]
theorem apCSOrderedStageVertex_processed
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool)
    (i : Fin r) :
    apCSOrderedStageVertex r s j bits
        (apCSOrderedStageProcessedVertexIndex r s j i) =
      bits i.succ := by
  unfold apCSOrderedStageVertex
  rw [dif_neg]
  · dsimp only [apCSOrderedStageProcessedVertexIndex]
    have ht :
        (finSuccAboveEquiv j).symm
            ⟨j.succAbove
                (csOrderedStageProcessedIndex r s i),
              Fin.succAbove_ne j
                (csOrderedStageProcessedIndex r s i)⟩ =
          csOrderedStageProcessedIndex r s i :=
      (finSuccAboveEquiv j).symm_apply_apply
        (csOrderedStageProcessedIndex r s i)
    rw [ht]
    simp [csOrderedStageProcessedIndex]
  · exact Fin.succAbove_ne j
      (csOrderedStageProcessedIndex r s i)



theorem apCSOrderedStageVertex_injective
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    Function.Injective
      (apCSOrderedStageVertex r s j) := by
  intro bits bits' hbits
  funext i
  refine Fin.cases ?_ (fun t => ?_) i
  · have h := congrFun hbits
      (apCSOrderedStageDistinguishedVertexIndex r s j)
    simpa using h
  · have h := congrFun hbits
      (apCSOrderedStageProcessedVertexIndex r s j t)
    simpa using h

noncomputable def apCSOrderedStageVertexEquiv
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    (Fin (r + 1) → Bool) ≃
      {ω : DeletedCube
          (((s + 1) + r) + 1)
          (apCSOrderedStageCurrentFace r s j) //
        ∃ bits : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits = ω} where
  toFun bits :=
    ⟨apCSOrderedStageVertex r s j bits,
      ⟨bits, rfl⟩⟩
  invFun ω :=
    Classical.choose ω.property
  left_inv bits := by
    apply apCSOrderedStageVertex_injective r s j
    exact Classical.choose_spec
      (show ∃ bits' : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits' =
            apCSOrderedStageVertex r s j bits
        from ⟨bits, rfl⟩)
  right_inv ω := by
    apply Subtype.ext
    exact Classical.choose_spec ω.property





/-- Expected stage selector, written without any arity casts. -/
noncomputable def apCSOrderedStageFaceExponent
    (r s : ℕ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1)) :
    LinearFormsExponent (((s + 1) + r) + 1) :=
  faceLinearFormsExponent
    (apCSOrderedStageCurrentFace r s j)
    (fun ω =>
      if active (apCSOrderedStageCurrentFace r s j) then
        if ∃ bits : Fin (r + 1) → Bool,
            apCSOrderedStageVertex r s j bits = ω
        then true
        else false
      else false)















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.apCSOrderedStageCubeEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.apCSOrderedStageDistinguishedVertexIndex.eq_1,
    `Wikipedia.SzemeredisTheorem.apCSOrderedStageVertex.eq_1,
    `Wikipedia.SzemeredisTheorem.apCSStageCubeTransportEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.apCSStageTransportJ.eq_1,
    `Wikipedia.SzemeredisTheorem.csConsInput.eq_1,
    `Wikipedia.SzemeredisTheorem.csConsInput.eq_2,
    `Wikipedia.SzemeredisTheorem.csConsInput.match_1,
    `Wikipedia.SzemeredisTheorem.csOrderedStageCurrentIndex.eq_1,
    `Wikipedia.SzemeredisTheorem.csOrderedStageFactorInput.eq_1,
    `Wikipedia.SzemeredisTheorem.csOrderedStageFactorInput.eq_2,
    `Wikipedia.SzemeredisTheorem.csOrderedStageFactorInput.eq_def,
    `Wikipedia.SzemeredisTheorem.csOrderedStageFactorInput.match_1,
    `Wikipedia.SzemeredisTheorem.csOrderedStageFutureIndex.eq_1,
    `Wikipedia.SzemeredisTheorem.csOrderedStageProcessedIndex.eq_1,
    `Wikipedia.SzemeredisTheorem.csPrependTuple.match_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


