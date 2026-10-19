-- Prove2me | Definitions.Def_AT260939824_EndpointCorrection
-- name    : AT260939824_EndpointCorrection
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:53:50.630779+00:00
-- url     : https://prove2.me/theorems/07193b61-3e17-4ce7-9daa-3406855a4440
-- title:
--   A final slot for a moving endpoint
-- statement:
--   In a real normed space $E$, a carry homotopy is reparametrized to reserve a final path slot. A linear segment then joins a fixed point $q$ to a continuously varying endpoint $e(r)$, where $r\in[0,1]$ is the deformation parameter. The corrected family remains in a set $S\subseteq E$ whenever the original carry and every inserted segment lie in $S$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/EndpointCorrection.lean, selected declaration lines 12-13, 15-19, 21-25, 27-31, 38-41, 43-45, 95-98, 100-108, 110-117; SHA-256 4096bae3a1eb6f9b5b92f3830f6071b8e6b16056e7f967981a805acf388d07e1. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
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

/-! Reserving the final path slot for a continuously moving endpoint. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def correctionCut (n : ℕ) : ℝ := ((n : ℝ)+1)/((n : ℝ)+2)
def correctionScale (n : ℕ) : ℝ≥0 := ⟨((n : ℝ)+2)/((n : ℝ)+1),by positivity⟩

theorem correctionCut_pos (n : ℕ) : 0 < correctionCut n := by unfold correctionCut; positivity
theorem correctionCut_lt_one (n : ℕ) : correctionCut n < 1 := by
  unfold correctionCut
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem correctionScale_cut (n : ℕ) : (correctionScale n : ℝ)*correctionCut n = 1 := by
  change (((n : ℝ)+2)/((n : ℝ)+1))*(((n : ℝ)+1)/((n : ℝ)+2)) = 1
  have h₁ : (n : ℝ)+1 ≠ 0 := by positivity
  have h₂ : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem correction_final_zero (n : ℕ) : ((n : ℝ)+2)*correctionCut n-((n : ℝ)+1) = 0 := by
  unfold correctionCut
  have h₂ : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring



def correctedCarryRaw (n : ℕ) (F : unitInterval × unitInterval → E) (q : E)
    (e : unitInterval → E) (z : unitInterval × ℝ) : E :=
  if z.2 ≤ correctionCut n then F (z.1,clampInterval ((correctionScale n : ℝ)*z.2))
  else mix q (e z.1) (clampInterval (((n : ℝ)+2)*z.2-((n : ℝ)+1)))

def correctedCarry (n : ℕ) (F : unitInterval × unitInterval → E) (q : E)
    (e : unitInterval → E) (z : unitInterval × unitInterval) : E :=
  correctedCarryRaw n F q e (z.1,z.2)





@[simp] theorem correctedCarry_source (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (r : unitInterval) :
    correctedCarry n F q e (r,0) = F (r,0) := by
  simp [correctedCarry,correctedCarryRaw,(correctionCut_pos n).le,clampInterval]

@[simp] theorem correctedCarry_target (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (r : unitInterval) :
    correctedCarry n F q e (r,1) = e r := by
  change (if (1 : ℝ) ≤ correctionCut n then _ else _) = _
  rw [if_neg (not_le.mpr (correctionCut_lt_one n))]
  change mix q (e r) (clampInterval (((n : ℝ)+2)*1-((n : ℝ)+1))) = e r
  have he : ((n : ℝ)+2)*1-((n : ℝ)+1) = 1 := by ring
  rw [he]
  simp [clampInterval]

theorem correctedCarry_mem {S : Set E} (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (hF : ∀ z, F z ∈ S)
    (hseg : ∀ r t, mix q (e r) t ∈ S) (z : unitInterval × unitInterval) :
    correctedCarry n F q e z ∈ S := by
  unfold correctedCarry correctedCarryRaw
  split
  · exact hF _
  · exact hseg _ _

end
end AbelianTargets.FixedSlots


