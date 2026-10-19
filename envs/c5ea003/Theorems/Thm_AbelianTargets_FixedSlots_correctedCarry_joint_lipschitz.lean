-- Prove2me | Theorems.Thm_AbelianTargets_FixedSlots_correctedCarry_joint_lipschitz
-- name    : AbelianTargets.FixedSlots.correctedCarry_joint_lipschitz
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:40:44.159299+00:00
-- url     : https://prove2.me/theorems/51a49096-eaaa-4a00-9099-93ef1171011a
-- title:
--   Finite joint Lipschitz control for a moving-endpoint correction
-- statement:
--   Let $E$ be a real normed vector space, $n\in\mathbb N$, and $J,C,\Delta\ge0$. Suppose $F:[0,1]^2\to E$ is $J$-Lipschitz for the maximum product metric, $e:[0,1]\to E$ is $C$-Lipschitz, and $q\in E$ satisfies
--   $$
--   F(r,1)=q,\qquad \|q-e(r)\|\le\Delta\quad(r\in[0,1]).
--   $$
--   Define $a_n=(n+1)/(n+2)$ and
--   $$
--   C_n(r,u)=
--   \begin{cases}
--   F\!\left(r,\dfrac{n+2}{n+1}u\right),&u\le a_n,\\
--   (1-t)q+t\,e(r),\quad t=(n+2)u-(n+1),&u>a_n.
--   \end{cases}
--   $$
--   Then there exists a finite $L\ge0$ such that
--   $$
--   \|C_n(r,u)-C_n(s,v)\|
--   \le L\max(|r-s|,|u-v|).
--   $$
--   The conclusion asserts existence of a joint bound and does not require a prescribed bound independent of the input data.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2.5 and 4, joint bounds for moving-endpoint interpolation supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/JointEndpointCorrection.lean, authoritative declaration span lines 73-100, SHA-256 0eabb5f246fec3bf7e0e296a3abe309abaa1fda72f09588a56462c4c8273d2c0. Frozen original source is local; no public repository URL or commit was available.

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

/-! Finite joint Lipschitz constants for the reserved endpoint slot. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AbelianTargets.FixedSlots.correctedCarry_joint_lipschitz (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) {J C Δ : ℝ≥0}
    (hF : LipschitzWith J F) (htarget : ∀ r, F (r,1) = q)
    (he : LipschitzWith C e) (hq : ∀ r, dist q (e r) ≤ Δ) :
    ∃ L : ℝ≥0, LipschitzWith L (correctedCarry n F q e) := by sorry
