-- Prove2me | Theorems.Thm_AbelianTargets_FixedSlots_rowFamily_joint_lipschitz
-- name    : AbelianTargets.FixedSlots.rowFamily_joint_lipschitz
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:41:31.822995+00:00
-- url     : https://prove2.me/theorems/7b24fa6a-7525-4fa7-8fa0-43ced5a1ca31
-- title:
--   Joint Lipschitz control of interpolated fixed-slot rows
-- statement:
--   Let $E$ be a real normed vector space, $n\in\mathbb N$, and $\Delta,C\ge0$. Let $a,b:\mathbb N\to E$ satisfy
--   $$
--   \|a_j-a_{j+1}\|\le\Delta,\quad
--   \|b_j-b_{j+1}\|\le\Delta\quad(0\le j\le n),
--   \qquad
--   \|a_j-b_j\|\le C\quad(0\le j\le n+1).
--   $$
--   For $r\in[0,1]$, set $v_j(r)=(1-r)a_j+rb_j$. Let $R(r,u)$ traverse the consecutive segments through $v_0(r),\ldots,v_{n+1}(r)$ in $n+1$ equal time intervals as $u$ runs from $0$ to $1$. Then, for the maximum product metric on $[0,1]^2$,
--   $$
--   \|R(r,u)-R(s,v)\|
--   \le\bigl(\Delta(n+1)+C\bigr)\max(|r-s|,|u-v|).
--   $$
--   No matching-endpoint condition between the two rows is assumed.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2.5 and 4, fixed-slot interpolation supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/VariableRowFamilies.lean, authoritative declaration span lines 31-48, SHA-256 b6ccb5ebcb474c04b50b84c15fa248c6b665da118530189a897b8c4c62bb42ec. Frozen original source is local; no public repository URL or commit was available.

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

/-! Fixed-slot row interpolation with a moving terminal vertex. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AbelianTargets.FixedSlots.rowFamily_joint_lipschitz (row₀ row₁ : ℕ → E) (n : ℕ) (Δ C : ℝ≥0)
    (h₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (h₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ)
    (hv : ∀ j ≤ n+1, dist (row₀ j) (row₁ j) ≤ C) :
    LipschitzWith (Δ*(n+1)+C) (rowFamily row₀ row₁ n) := by sorry
