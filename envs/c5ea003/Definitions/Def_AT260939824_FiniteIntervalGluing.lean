-- Prove2me | Definitions.Def_AT260939824_FiniteIntervalGluing
-- name    : AT260939824_FiniteIntervalGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:09:01.369103+00:00
-- url     : https://prove2.me/theorems/1c4429fc-9420-4b94-b03a-f0280314e464
-- title:
--   Literal gluing on finitely many intervals
-- statement:
--   A family of maps $F_i:[0,1]^2\to Z$ is assembled along finitely many consecutive unit intervals in its first parameter. The construction chooses fixed endpoint values outside the assembled interval and uses the prescribed map within each slot. If every relevant $F_i$ takes values in a set $S\subseteq Z$, then the assembled family also takes values in $S$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/FiniteIntervalGluing.lean, selected declaration lines 11-14, 27-33, 126-135, 144-153; SHA-256 5223a40c3d087f2855d66f30d60652c97fd663835a7124935816e07d5192aac6. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! Finite families on neighboring unit intervals glue literally.
Their path-time Lipschitz constant is independent of the number of intervals. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {Z : Type*} [MetricSpace Z]

def intervalGlue (F : ℕ → unitInterval × unitInterval → Z) : ℕ → ℝ × unitInterval → Z
  | 0 => fun z => F 0 (clampInterval z.1,z.2)
  | n+1 => fun z => if z.1 ≤ (n : ℝ)+1 then intervalGlue F n z
      else F (n+1) (clampInterval (z.1-((n : ℝ)+1)),z.2)



theorem intervalGlue_zero (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (u : unitInterval) : intervalGlue F n (0,u) = F 0 (0,u) := by
  induction n with
  | zero => simp [intervalGlue,clampInterval]
  | succ n ih =>
    simp only [intervalGlue]
    rw [if_pos (by positivity),ih]









theorem intervalGlue_mem {S : Set Z} (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (hF : ∀ i ≤ n, ∀ z, F i z ∈ S) (z : ℝ × unitInterval) :
    intervalGlue F n z ∈ S := by
  induction n with
  | zero => exact hF 0 le_rfl _
  | succ n ih =>
    unfold intervalGlue
    split
    · exact ih (fun i hi => hF i (by omega))
    · exact hF (n+1) le_rfl _



theorem intervalGlue_eval_eq (F G : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (u : unitInterval) (h : ∀ i ≤ n, ∀ r, F i (r,u) = G i (r,u)) (x : ℝ) :
    intervalGlue F n (x,u) = intervalGlue G n (x,u) := by
  induction n with
  | zero => exact h 0 le_rfl _
  | succ n ih =>
    simp only [intervalGlue]
    split
    · exact ih (fun i hi => h i (by omega))
    · exact h (n+1) le_rfl _

end
end AbelianTargets.FixedSlots


