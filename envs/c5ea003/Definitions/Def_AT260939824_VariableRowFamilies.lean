-- Prove2me | Definitions.Def_AT260939824_VariableRowFamilies
-- name    : AT260939824_VariableRowFamilies
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:53:15.407216+00:00
-- url     : https://prove2.me/theorems/a7ec7ba0-7ab1-4132-8bc7-e593afc8117d
-- title:
--   Affine interpolation between equal-slot row paths
-- statement:
--   Let $E$ be a real normed vector space and $a^0,a^1:\mathbb N\to E$ two rows. For $n\in\mathbb N$ define a two-parameter family by traversing the $n+1$ affine edges of the interpolated vertices:
--   $$F(r,t)=\operatorname{rowPath}_{n+1}\bigl(j\mapsto(1-r)a^0_j+ra^1_j\bigr)(t).$$
--   Suppose that for each $j\le n$, a convex set $C_j\subseteq S\subseteq E$ contains the four vertices $a^0_j,a^0_{j+1},a^1_j,a^1_{j+1}$. Then $F(r,t)\in S$ for every $r,t\in I$. The construction retains equal path-time slots as the row varies. At $r=0$ and $r=1$ the family equals the two original row paths. Its path endpoints are $F(r,0)=(1-r)a^0_0+ra^1_0$ and $F(r,1)=(1-r)a^0_{n+1}+ra^1_{n+1}$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/VariableRowFamilies.lean, selected declaration lines 12-13, 50-60, 62-65, 67-70, 72-74, 76-80; SHA-256 b6ccb5ebcb474c04b50b84c15fa248c6b665da118530189a897b8c4c62bb42ec. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RelativePathContraction
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

/-! Fixed-slot row interpolation with a moving terminal vertex. -/

namespace AbelianTargets.FixedSlots

open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rowFamily (row₀ row₁ : ℕ → E) (n : ℕ) (z : unitInterval × unitInterval) : E :=
  rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) z.1) n z.2







theorem rowFamily_mem_charts (row₀ row₁ : ℕ → E) (n : ℕ) {S : Set E}
    (hcharts : ∀ j ≤ n, ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧
      row₀ j ∈ F ∧ row₀ (j+1) ∈ F ∧ row₁ j ∈ F ∧ row₁ (j+1) ∈ F)
    (z : unitInterval × unitInterval) : rowFamily row₀ row₁ n z ∈ S := by
  have hne : (n : ℝ)+1 ≠ 0 := by positivity
  have hu : (z.2 : ℝ) ≤ ((n : ℝ)+1)/((n+1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add,Nat.cast_one,hne] using z.2.property.2
  obtain ⟨j,hj,h₀,h₁⟩ := exists_slot (n+1) (Nat.succ_pos n) n z.2 z.2.property.1 hu
  obtain ⟨F,hconv,hsub,ha,hb,hc,hd⟩ := hcharts j hj
  exact hsub (interpolated_row_mem_on_slot (n+1) (Nat.succ_pos n) row₀ row₁ n j hj z.1
    hconv ha hb hc hd z.2 h₀ h₁)

@[simp] theorem rowFamily_zero (row₀ row₁ : ℕ → E) (n : ℕ) (u : unitInterval) :
    rowFamily row₀ row₁ n (0,u) = asPath row₀ n u := by
  simp only [rowFamily,mix_zero]
  rfl

@[simp] theorem rowFamily_one (row₀ row₁ : ℕ → E) (n : ℕ) (u : unitInterval) :
    rowFamily row₀ row₁ n (1,u) = asPath row₁ n u := by
  simp only [rowFamily,mix_one]
  rfl

@[simp] theorem rowFamily_source (row₀ row₁ : ℕ → E) (n : ℕ) (r : unitInterval) :
    rowFamily row₀ row₁ n (r,0) = mix (row₀ 0) (row₁ 0) r :=
  rowPath_zero (n+1) (Nat.succ_pos n) _ n

@[simp] theorem rowFamily_target (row₀ row₁ : ℕ → E) (n : ℕ) (r : unitInterval) :
    rowFamily row₀ row₁ n (r,1) = mix (row₀ (n+1)) (row₁ (n+1)) r := by
  have h := rowPath_right (n+1) (Nat.succ_pos n) (fun j => mix (row₀ j) (row₁ j) r) n
  have he : ((n : ℝ)+1)/(n+1 : ℕ) = 1 := by push_cast; field_simp
  simpa only [rowFamily,he] using h

end
end AbelianTargets.FixedSlots


