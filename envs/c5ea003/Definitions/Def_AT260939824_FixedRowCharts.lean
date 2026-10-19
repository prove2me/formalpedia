-- Prove2me | Definitions.Def_AT260939824_FixedRowCharts
-- name    : AT260939824_FixedRowCharts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:59:59.70608+00:00
-- url     : https://prove2.me/theorems/c84fc240-1005-4b0a-b618-5d4311fb5032
-- title:
--   Four-corner certificates for contextual row moves
-- statement:
--   Let $V$ be a vertex set and let a downward-closed predicate specify its admissible finite faces. Replacing the middle entry of a three-vertex segment inside a larger valid row leaves every other entry unchanged. If the four replacement vertices form one admissible face, each corresponding pair of old and new edges also lies in one admissible face. These facts supply the convex charts used to realize row replacements.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/FixedRowCharts.lean, selected declaration lines 9-13, 15-19, 21-25, 27-44, 46-75; SHA-256 c603d78a59131ea62ea74daae8f8ee3fae093a55fb130015bd9ef35dec22a28b. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CanonicalRows
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_RowValidity
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

/-! Four-corner simplex certificates for contextual equal-slot replacements. -/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

theorem contextual_getD_first (p s : List V) (a b c d : V) :
    (p ++ [a,b,c] ++ s).getD p.length d = a := by
  induction p with
  | nil => rfl
  | cons v p ih => simpa only [List.length_cons,List.cons_append,List.getD_cons_succ] using ih

theorem contextual_getD_middle (p s : List V) (a b c d : V) :
    (p ++ [a,b,c] ++ s).getD (p.length+1) d = b := by
  induction p with
  | nil => rfl
  | cons v p ih => simpa only [List.length_cons,List.cons_append,List.getD_cons_succ] using ih

theorem contextual_getD_third (p s : List V) (a b c d : V) :
    (p ++ [a,b,c] ++ s).getD (p.length+2) d = c := by
  induction p with
  | nil => rfl
  | cons v p ih => simpa only [List.length_cons,List.cons_append,List.getD_cons_succ] using ih

theorem contextual_getD_unchanged (p s : List V) (a b b' c d : V) (j : ℕ)
    (hj : j ≠ p.length+1) :
    (p ++ [a,b,c] ++ s).getD j d = (p ++ [a,b',c] ++ s).getD j d := by
  induction p generalizing j with
  | nil =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => exact False.elim (hj rfl)
      | succ j => rfl
  | cons v p ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [List.cons_append,List.getD_cons_succ] using ih j (by
        simp only [List.length_cons] at hj
        omega)

theorem contextual_four_corners_face (hd : FaceDownward Face)
    (p s : List V) (a b b' c z : V) (hf : Face {a,b,b',c})
    (hv : ValidRow Face (p ++ [a,b,c] ++ s)) (j : ℕ)
    (hj : j+1 < (p ++ [a,b,c] ++ s).length) :
    Face {(p ++ [a,b,c] ++ s).getD j z,
      (p ++ [a,b,c] ++ s).getD (j+1) z,
      (p ++ [a,b',c] ++ s).getD j z,
      (p ++ [a,b',c] ++ s).getD (j+1) z} := by
  by_cases h₀ : j = p.length
  · subst j
    rw [contextual_getD_first,contextual_getD_middle,
      contextual_getD_first,contextual_getD_middle]
    apply hd hf
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
    obtain rfl | rfl | rfl | rfl := hv <;> simp
  · by_cases h₁ : j = p.length+1
    · subst j
      rw [contextual_getD_middle,contextual_getD_third,
        contextual_getD_middle,contextual_getD_third]
      apply hd hf
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      obtain rfl | rfl | rfl | rfl := hv <;> simp
    · rw [← contextual_getD_unchanged p s a b b' c z j h₁,
        ← contextual_getD_unchanged p s a b b' c z (j+1) (by omega)]
      apply hd (hv.edge_getD z j hj)
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      tauto

end AbelianTargets


