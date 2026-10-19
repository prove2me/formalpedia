-- Prove2me | Theorems.Thm_AbelianTargets_FixedSlots_intervalGlue_on_unit
-- name    : AbelianTargets.FixedSlots.intervalGlue_on_unit
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:42:12.563563+00:00
-- url     : https://prove2.me/theorems/05a906a8-1d08-45b2-84bb-1aa60cfb3e08
-- title:
--   Restriction of sequential gluing to each unit interval
-- statement:
--   Let $Z$ be a metric space and let $F_j:[0,1]^2\to Z$ be a family indexed by $j\in\mathbb N$. For $N\in\mathbb N$, define the sequential gluing $G_N:\mathbb R\times[0,1]\to Z$ using the clamp $\rho(t)=\min(1,\max(0,t))$:
--   $$
--   G_0(x,u)=F_0(\rho(x),u),\qquad
--   G_{k+1}(x,u)=
--   \begin{cases}
--   G_k(x,u),&x\le k+1,\\
--   F_{k+1}(\rho(x-k-1),u),&x>k+1.
--   \end{cases}
--   $$
--   Assume adjacent families match:
--   $$
--   F_j(1,u)=F_{j+1}(0,u)\qquad(j<N,\ u\in[0,1]).
--   $$
--   For every $i\le N$ and $s,u\in[0,1]$,
--   $$
--   G_N(i+s,u)=F_i(s,u).
--   $$
--   This includes the shared endpoints and $N=0$. No continuity or Lipschitz hypothesis on the families is required.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 4, literal finite-interval interpolation supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/FiniteIntervalGluing.lean, authoritative declaration span lines 35-61, SHA-256 5223a40c3d087f2855d66f30d60652c97fd663835a7124935816e07d5192aac6. Frozen original source is local; no public repository URL or commit was available.

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

theorem AbelianTargets.FixedSlots.intervalGlue_on_unit (F : ℕ → unitInterval × unitInterval → Z) (N i : ℕ)
    (hi : i ≤ N) (hmatch : ∀ j < N, ∀ u, F j (1,u) = F (j+1) (0,u))
    (s u : unitInterval) : intervalGlue F N ((i : ℝ)+s,u) = F i (s,u) := by sorry
