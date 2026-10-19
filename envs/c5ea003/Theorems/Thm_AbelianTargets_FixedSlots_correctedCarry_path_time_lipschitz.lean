-- Prove2me | Theorems.Thm_AbelianTargets_FixedSlots_correctedCarry_path_time_lipschitz
-- name    : AbelianTargets.FixedSlots.correctedCarry_path_time_lipschitz
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:41:48.453983+00:00
-- url     : https://prove2.me/theorems/3e195aa7-3e9d-4320-a5ac-c1be874d541e
-- title:
--   Time-speed bound after reserving one moving-endpoint slot
-- statement:
--   Let $E$ be a real normed vector space, $n\in\mathbb N$, $\Delta\ge0$, $F:[0,1]^2\to E$, $q\in E$, and $e:[0,1]\to E$. Assume each path $u\mapsto F(r,u)$ is $\Delta(n+1)$-Lipschitz, and
--   $$
--   F(r,1)=q,\qquad \|q-e(r)\|\le\Delta\quad(r\in[0,1]).
--   $$
--   Put $a_n=(n+1)/(n+2)$ and define
--   $$
--   C_n(r,u)=
--   \begin{cases}
--   F\!\left(r,\dfrac{n+2}{n+1}u\right),&u\le a_n,\\
--   (1-t)q+t\,e(r),\quad t=(n+2)u-(n+1),&u>a_n.
--   \end{cases}
--   $$
--   For every fixed $r$, the corrected path satisfies
--   $$
--   \|C_n(r,u)-C_n(r,v)\|\le\Delta(n+2)|u-v|.
--   $$
--   No regularity in the parameter $r$ is required for this time-direction estimate.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2.5 and 4, fixed-slot moving-endpoint interpolation supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/EndpointCorrection.lean, authoritative declaration span lines 70-93, SHA-256 4096bae3a1eb6f9b5b92f3830f6071b8e6b16056e7f967981a805acf388d07e1. Frozen original source is local; no public repository URL or commit was available.

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

/-! Reserving the final path slot for a continuously moving endpoint. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AbelianTargets.FixedSlots.correctedCarry_path_time_lipschitz (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (Δ : ℝ≥0)
    (hF : ∀ r, LipschitzWith (Δ*(n+1)) (fun u : unitInterval => F (r,u)))
    (htarget : ∀ r, F (r,1) = q) (he : ∀ r, dist q (e r) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+2)) (fun u : unitInterval => correctedCarry n F q e (r,u)) := by sorry
