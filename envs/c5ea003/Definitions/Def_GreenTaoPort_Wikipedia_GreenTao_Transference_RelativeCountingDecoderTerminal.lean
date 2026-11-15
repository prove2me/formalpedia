-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderTerminal
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderTerminal
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:11:31.713578+00:00
-- url     : https://prove2.me/theorems/5093b2f6-c44d-467d-b87d-b7183720aa32
-- title:
--   Terminal products and cube equivalences for the counting decoder
-- statement:
--   For a majorized cut system $S$ of arity $n$, its terminal core product multiplies the original core over all Boolean choices of $n$ endpoint pairs. The terminal majorant product multiplies every designated majorant over its full deleted-coordinate cube. A terminal iterator eliminates all live coordinates; its decoded version has external parameter $P\times(G\times G)^n$ and zero remaining arity.
--
--   The bundle also supplies arity transport, zero-stage and successor-stage equivalences, and an equivalence appending one endpoint pair to the nested parameter. For AP systems, the decoded terminal parameter is equivalent to the full doubled cube, with the base pair at the distinguished coordinate. A further equivalence identifies the Boolean encoding of each nondistinguished face vertex with that face’s deleted cube.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingDecoderTerminal.lean#L31-L580

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderStep
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
# Terminal identities for the relative-counting decoder

This file closes the algebraic end of the mixed Cauchy--Schwarz recursion.
After every deleted coordinate has been doubled, the nested parameter is a
full Boolean AP cube.  The terminal core consists of the centered product
on the distinguished face and one copy of every vertex on each active
non-distinguished face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem



/-- Product of all Boolean copies of the original core at a fully decoded
terminal parameter. -/
noncomputable def terminalCoreProduct
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (p : P) (a : Fin n → G × G) : ℝ :=
  ∏ bits : Fin n → Bool,
    S.core p (fun i => selectPair (a i) (bits i))

/-- Product of every original designated majorant at every vertex of its
deleted-coordinate cube. -/
noncomputable def terminalMajorantProduct
    {P G : Type u} :
    ∀ {n : ℕ},
      MajorizedCutSystem P G n →
      P → (Fin n → G × G) → ℝ
  | 0, _S, _p, _a => 1
  | n + 1, S, p, a =>
      ∏ i : Fin (n + 1),
        ∏ bits : Fin n → Bool,
          S.majorant p i
            (eraseCoordinate i
              (fun q =>
                selectPair (a q)
                  (@Fin.insertNth n
                    (fun _ => Bool) i false bits q)))





/-- Apply `next` through every live coordinate, without introducing the
`0 + n` cast required by the more general two-index iterator. -/
def iterNextTerminal
    {P G : Type u} :
    ∀ n : ℕ,
      MajorizedCutSystem P G n →
        MajorizedCutSystem (CSStageParam P G n) G 0
  | 0, S => S
  | n + 1, S => iterNextTerminal n S.next

/-- The fully iterated system with its nested parameter decoded into the
original parameter and one endpoint pair for each eliminated coordinate. -/
def iterNextTerminalDecoded
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n) :
    MajorizedCutSystem (P × (Fin n → G × G)) G 0 :=
  (iterNextTerminal n S).reindex
    (csStageParamEquiv P G n).symm

/-- Transport only the live-coordinate arity of a cut system. -/
def castArity
    {P G : Type u} {m n : ℕ}
    (h : m = n)
    (S : MajorizedCutSystem P G m) :
    MajorizedCutSystem P G n :=
  h ▸ S





/-- The zero-stage nested parameter is the original parameter. -/
def csStageZeroEquiv
    (P G : Type u) :
    CSStageParam P G 0 ≃ P :=
  Equiv.refl P

/-- Expose the definitional successor equation of `CSStageParam` as an
equivalence so finite instances can be transported explicitly. -/
def csStageSuccNativeEquiv
    (P G : Type u) (r : ℕ) :
    CSStageParam P G (r + 1) ≃
      CSStageParam (P × (G × G)) G r :=
  Equiv.refl _





/-- The same reassociation in the native nested representation.  Its
recursive definition makes compatibility with `iterNext` transparent. -/
def csStageAppendPairEquiv
    (P G : Type u) :
    ∀ r : ℕ,
      (CSStageParam P G r × (G × G)) ≃
        CSStageParam P G (r + 1)
  | 0 => Equiv.refl (P × (G × G))
  | r + 1 =>
      csStageAppendPairEquiv
        (P × (G × G)) G r













end MajorizedCutSystem

/-! ## The terminal AP cube and its face vertices -/

/-- A decoded terminal parameter is exactly a doubled AP cube: the base
pair occupies the distinguished coordinate and the remaining endpoint
pairs occupy its canonical `succAbove` complement. -/
def apCSTerminalCubeEquiv
    (n N : ℕ) (j : Fin (n + 1)) :
    ((Bool → ZMod N) ×
        (Fin n → ZMod N × ZMod N)) ≃
      CubePoint (n + 1) N where
  toFun q :=
    Fin.insertNth j q.1
      (fun t => selectPair (q.2 t))
  invFun x :=
    (x j,
      fun t =>
        (x (j.succAbove t) false,
          x (j.succAbove t) true))
  left_inv q := by
    rcases q with ⟨a, pairs⟩
    apply Prod.ext
    · funext b
      simp
    · funext t
      exact Prod.ext (by simp) (by simp)
  right_inv x := by
    apply (Fin.insertNth_eq_iff).2
    constructor
    · funext b
      simp
    · funext t b
      cases b <;> rfl





/-- The vertex on face `j.succAbove t` encoded by a choice at `j` and
choices on all deleted coordinates other than `t`. -/
noncomputable def apCSTerminalFaceVertex
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (bits : Bool × (Fin m → Bool)) :
    DeletedCube ((m + 1) + 1) (j.succAbove t) :=
  fun q =>
    if hq : q.1 = j then
      bits.1
    else
      let d :=
        (finSuccAboveEquiv j).symm
          ⟨q.1, hq⟩
      have hjd : j.succAbove d = q.1 := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv j).apply_symm_apply
            ⟨q.1, hq⟩)
      have hdt : d ≠ t := by
        intro h
        apply q.2
        rw [← hjd, h]
      bits.2
        ((finSuccAboveEquiv t).symm
          ⟨d, hdt⟩)

/-- The preceding face-vertex encoding is a genuine equivalence, not only
a surjection used under a product. -/
noncomputable def apCSTerminalFaceVertexEquiv
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1)) :
    (Bool × (Fin m → Bool)) ≃
      DeletedCube ((m + 1) + 1)
        (j.succAbove t) where
  toFun := apCSTerminalFaceVertex m j t
  invFun ω :=
    (ω ⟨j, (Fin.succAbove_ne j t).symm⟩,
      fun r =>
        ω ⟨j.succAbove (t.succAbove r), by
          intro h
          exact (Fin.succAbove_ne t r)
            (Fin.succAbove_right_injective h)⟩)
  left_inv bits := by
    apply Prod.ext
    · simp [apCSTerminalFaceVertex]
    · funext r
      change (if h : j.succAbove (t.succAbove r) = j then _ else _) = _
      rw [dif_neg (Fin.succAbove_ne j (t.succAbove r))]
      apply congrArg bits.2
      apply (finSuccAboveEquiv t).injective
      rw [(finSuccAboveEquiv t).apply_symm_apply]
      apply Subtype.ext
      apply (finSuccAboveEquiv j).injective
      rw [(finSuccAboveEquiv j).apply_symm_apply]
      apply Subtype.ext
      rfl
  right_inv ω := by
    funext q
    by_cases hq : q.1 = j
    · have hqeq :
          q = ⟨j, (Fin.succAbove_ne j t).symm⟩ := by
        apply Subtype.ext
        exact hq
      rw [hqeq]
      simp [apCSTerminalFaceVertex]
    · let d :=
        (finSuccAboveEquiv j).symm
          ⟨q.1, hq⟩
      have hjd : j.succAbove d = q.1 := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv j).apply_symm_apply
            ⟨q.1, hq⟩)
      have hdt : d ≠ t := by
        intro h
        apply q.2
        rw [← hjd, h]
      let r :=
        (finSuccAboveEquiv t).symm
          ⟨d, hdt⟩
      have htr : t.succAbove r = d := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv t).apply_symm_apply
            ⟨d, hdt⟩)
      change
        (if h : q.1 = j then _ else _) = _
      rw [dif_neg hq]
      apply congrArg ω
      apply Subtype.ext
      change j.succAbove (t.succAbove r) = q.1
      rw [htr, hjd]









namespace MajorizedCutSystem

























end MajorizedCutSystem

/-! ## Quantitative active-mask endpoint -/



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.castArity.congr_simp,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.csStageAppendPairEquiv.match_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.csStageSuccNativeEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.csStageZeroEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.iterNextTerminal.match_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.terminalCoreProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.terminalMajorantProduct.match_1,
    `Wikipedia.SzemeredisTheorem.apCSTerminalCubeEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.apCSTerminalFaceVertex.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


