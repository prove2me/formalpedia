-- Prove2me | Definitions.Def_AT260939824_RowSlotScaling
-- name    : AT260939824_RowSlotScaling
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:55:56.737071+00:00
-- url     : https://prove2.me/theorems/eb61fb8d-82d0-4105-879e-71df8e7c10f5
-- title:
--   Appending an endpoint to a finite affine row path
-- statement:
--   Let $E$ be a real normed vector space, let $a:\mathbb N\to E$ be a row, $n\in\mathbb N$, and $e\in E$. Define the appended row by
--   $$a'_j=\begin{cases}a_j&j\le n+1,\\e&j>n+1.\end{cases}$$
--   Thus its row path with $n+2$ equal affine slots traverses the old vertices $a_0,\ldots,a_{n+1}$ and then the new endpoint $e$. This definition is used in identifying the initial rescaled path and final affine carry segment with one enlarged row path. More precisely, if a family $F(r,u)$ equals the old $(n+1)$-slot row path at a fixed parameter $r$ and $a_{n+1}=q$, then its corrected carry with appended endpoint $e(r)$ equals the enlarged $(n+2)$-slot path for every $u\in[0,1]$. The prefix is rescaled at the cut $(n+1)/(n+2)$, and the final slot is the affine segment $q\to e(r)$. The selected row congruence and scaling identities justify this equality without continuity assumptions on the family.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RowSlotScaling.lean, selected declaration lines 9-14, 16-28, 30-37, 39-40, 42-89; SHA-256 2b03c35dc4cf41d7c65702c25b581c1675949d340a286f9ea7780f9f0c1207f1. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
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

/-! Literal equality of normalized row paths after reserving a final slot. -/

namespace AbelianTargets.FixedSlots
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineSlot_scale (T S : ℕ) (hS : 0 < S) (row : ℕ → E) (j : ℕ) (u : ℝ) :
    affineSlot T row j u = affineSlot S row j (((T : ℝ)/S)*u) := by
  unfold affineSlot
  congr 1
  have hne : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  field_simp

theorem rowPath_scale (T S : ℕ) (hT : 0 < T) (hS : 0 < S) (row : ℕ → E)
    (k : ℕ) (u : ℝ) : rowPath T row k u = rowPath S row k (((T : ℝ)/S)*u) := by
  induction k with
  | zero => exact affineSlot_scale T S hS row 0 u
  | succ k ih =>
    have hcut : u ≤ ((k : ℝ)+1)/T ↔ ((T : ℝ)/S)*u ≤ ((k : ℝ)+1)/S := by
      have hT' : (0 : ℝ) < T := by exact_mod_cast hT
      have hS' : (0 : ℝ) < S := by exact_mod_cast hS
      rw [le_div_iff₀ hT',le_div_iff₀ hS']
      have he : (((T : ℝ)/S)*u)*S = u*T := by
        field_simp
      rw [he]
    simp only [rowPath,←hcut,ih,affineSlot_scale T S hS]

theorem rowPath_congr (T : ℕ) (row₀ row₁ : ℕ → E) (k : ℕ)
    (h : ∀ j ≤ k+1, row₀ j = row₁ j) (u : ℝ) :
    rowPath T row₀ k u = rowPath T row₁ k u := by
  induction k with
  | zero => simp only [rowPath,affineSlot,h 0 (by omega),h 1 le_rfl]
  | succ k ih =>
    simp only [rowPath,ih (fun j hj => h j (by omega)),affineSlot,
      h (k+1) (by omega),h (k+1+1) le_rfl]

def appendRowEndpoint (row : ℕ → E) (n : ℕ) (e : E) (j : ℕ) : E :=
  if j ≤ n+1 then row j else e

theorem correctedCarry_row_eq (n : ℕ) (row : ℕ → E) (q : E) (e : unitInterval → E)
    (F : unitInterval × unitInterval → E) (r : unitInterval)
    (hF : ∀ u, F (r,u) = asPath row n u) (hq : row (n+1) = q) (u : unitInterval) :
    correctedCarry n F q e (r,u) = asPath (appendRowEndpoint row n (e r)) (n+1) u := by
  change (if (u : ℝ) ≤ correctionCut n then _ else _) =
    (if (u : ℝ) ≤ ((n : ℝ)+1)/(n+1+1 : ℕ) then _ else _)
  have hecut : ((n : ℝ)+1)/(n+1+1 : ℕ) = correctionCut n := by
    simp only [correctionCut,Nat.cast_add,Nat.cast_one]
    ring_nf
  rw [hecut]
  split_ifs with hu
  · rw [hF]
    have htime : 0 ≤ (correctionScale n : ℝ)*(u : ℝ) ∧
        (correctionScale n : ℝ)*(u : ℝ) ≤ 1 := by
      refine ⟨mul_nonneg (correctionScale n).property u.property.1,?_⟩
      calc
        _ ≤ (correctionScale n : ℝ)*correctionCut n :=
          mul_le_mul_of_nonneg_left hu (correctionScale n).property
        _ = 1 := correctionScale_cut n
    have hc : clampInterval ((correctionScale n : ℝ)*(u : ℝ)) =
        ⟨(correctionScale n : ℝ)*(u : ℝ),htime⟩ := clampInterval_coe ⟨_,htime⟩
    rw [hc]
    change rowPath (n+1) row n ((correctionScale n : ℝ)*(u : ℝ)) = _
    have hs : (correctionScale n : ℝ) = (n+2 : ℕ)/(n+1 : ℕ) := by
      simp only [correctionScale,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      rfl
    rw [hs]
    rw [← rowPath_scale (n+2) (n+1) (by omega) (by omega)]
    apply rowPath_congr
    intro j hj
    simp only [appendRowEndpoint,if_pos hj]
  · have htime : 0 ≤ ((n : ℝ)+2)*(u : ℝ)-((n : ℝ)+1) ∧
        ((n : ℝ)+2)*(u : ℝ)-((n : ℝ)+1) ≤ 1 := by
      have hu' : correctionCut n ≤ (u : ℝ) := le_of_lt (lt_of_not_ge hu)
      have hh := mul_le_mul_of_nonneg_left hu' (show (0 : ℝ) ≤ (n : ℝ)+2 by positivity)
      rw [show ((n : ℝ)+2)*correctionCut n = (n : ℝ)+1 by
        have := correction_final_zero n
        linarith] at hh
      have hh' := mul_le_mul_of_nonneg_left u.property.2
        (show (0 : ℝ) ≤ (n : ℝ)+2 by positivity)
      constructor <;> linarith
    rw [show clampInterval (((n : ℝ)+2)*(u : ℝ)-((n : ℝ)+1)) =
      ⟨_,htime⟩ from clampInterval_coe ⟨_,htime⟩]
    unfold affineSlot mix
    simp only [appendRowEndpoint,if_pos (le_refl (n+1)),
      if_neg (show ¬n+1+1 ≤ n+1 by omega),hq,Nat.cast_add,Nat.cast_one]
    rw [show (n : ℝ)+1+1 = (n : ℝ)+2 by ring]
    exact (AffineMap.lineMap_apply_module _ _ _).symm

end
end AbelianTargets.FixedSlots


