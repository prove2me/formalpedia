-- Prove2me | Theorems.Thm_AbelianTargets_FixedSlots_intervalGlue_joint_lipschitz
-- name    : AbelianTargets.FixedSlots.intervalGlue_joint_lipschitz
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:42:10.16002+00:00
-- url     : https://prove2.me/theorems/ddf40d1b-9723-4046-8ef4-3009c14b1bcc
-- title:
--   Finite joint Lipschitz control for sequential interval gluing
-- statement:
--   Let $Z$ be a metric space, $n\in\mathbb N$, and $F_i:[0,1]^2\to Z$ for $i\in\mathbb N$. Suppose each $F_i$ with $i\le n$ has some finite nonnegative Lipschitz constant for the maximum product metric, and
--   $$
--   F_i(1,u)=F_{i+1}(0,u)\qquad(i<n,\ u\in[0,1]).
--   $$
--   Glue the families successively along the intervals $[i,i+1]$, using constant extension in the first coordinate outside the two outer endpoints. Thus
--   $$
--   G_n(x,u)=F_i(x-i,u)\quad(i\le x\le i+1,\ 0\le i\le n),
--   $$
--   with $G_n(x,u)=F_0(0,u)$ for $x\le0$ and $G_n(x,u)=F_n(1,u)$ for $x\ge n+1$. The seam identities make these formulas consistent. Then
--   $$
--   \exists J\ge0,\qquad
--   d(G_n(x,u),G_n(y,v))
--   \le J\max(|x-y|,|u-v|).
--   $$
--   The conclusion is existence of a finite joint bound, with no asserted uniform bound independent of $n$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2.5 and 4, finite-interval joint bounds supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/FiniteIntervalGluing.lean, authoritative declaration span lines 94-124, SHA-256 5223a40c3d087f2855d66f30d60652c97fd663835a7124935816e07d5192aac6. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteIntervalGluing
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
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {Z : Type*} [MetricSpace Z]

theorem AbelianTargets.FixedSlots.intervalGlue_joint_lipschitz (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (hF : ∀ i ≤ n, ∃ J : ℝ≥0, LipschitzWith J (F i))
    (hmatch : ∀ i < n, ∀ u, F i (1,u) = F (i+1) (0,u)) :
    ∃ J : ℝ≥0, LipschitzWith J (intervalGlue F n) := by sorry
