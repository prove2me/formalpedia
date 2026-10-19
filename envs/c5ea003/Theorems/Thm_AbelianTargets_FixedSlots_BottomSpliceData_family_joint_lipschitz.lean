-- Prove2me | Theorems.Thm_AbelianTargets_FixedSlots_BottomSpliceData_family_joint_lipschitz
-- name    : AbelianTargets.FixedSlots.BottomSpliceData.family_joint_lipschitz
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:41:50.583238+00:00
-- url     : https://prove2.me/theorems/de65399e-ba3c-4ad1-a055-699f29f910dc
-- title:
--   A bottom-edge splice has a finite joint Lipschitz bound
-- statement:
--   Let $E$ be a real normed vector space, $n\in\mathbb N$, $b,p,q\in E$, $S\subseteq E$, and $\Delta\ge0$. Consider bottom-splice data consisting of a left row of $n+3$ vertices from $b$ to $p$, source and target rows of $n+2$ vertices from $b$ to $q$, and an endpoint-fixed homotopy $H$ between their affine row paths. Assume all left-row and seam-row edges have length at most $\Delta$, where the seam row appends $(p+q)/2$ to the source row; each corresponding pair of row edges lies in a convex subset of $S$; corresponding row vertices have a common finite distance bound; $\operatorname{dist}(p,q)\le\Delta$ and $p,q$ lie in a convex subset of $S$; $H$ takes values in $S$, has path-time Lipschitz bound $\Delta(n+1)$, and has some finite joint Lipschitz bound. The splice family $F:I^2\to E$ uses the affine interpolation from the left row to the seam row in its first half and the corrected carry of $H$, with endpoint $(1-t)p+tq$, in its second half. With the maximum metric on $I^2$, there exists $J\ge0$ such that
--   $$
--   \operatorname{dist}(F(r,u),F(r',u'))\le J\max\{|r-r'|,|u-u'|\}
--   \qquad(r,u,r',u'\in I).
--   $$
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/BottomEdgeSplice.lean, lines 90–101; SHA256 52ee5fad572bee063a7c8d5d7961cbf69683a2cd2a80d8a9a1c13678b8c3a44f.

import Definitions.Def_AT260939824_BottomEdgeSplice
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

/-! The complete moving-endpoint family across one bottom edge. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace AbelianTargets.FixedSlots.BottomSpliceData
end AbelianTargets.FixedSlots.BottomSpliceData
open AbelianTargets
open AbelianTargets.FixedSlots
open AbelianTargets.FixedSlots.BottomSpliceData
variable {n : ℕ} {base p q : E} {S : Set E} {Δ : ℝ≥0}
variable (D : BottomSpliceData n base p q S Δ)

theorem AbelianTargets.FixedSlots.BottomSpliceData.family_joint_lipschitz : ∃ J : ℝ≥0, LipschitzWith J D.family := by sorry
