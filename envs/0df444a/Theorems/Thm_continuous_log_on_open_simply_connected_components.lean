-- Prove2me | Theorems.Thm_continuous_log_on_open_simply_connected_components
-- name    : continuous_log_on_open_simply_connected_components
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T03:23:21.296251+00:00
-- url     : https://prove2.me/theorems/adf7f4e2-5633-4dca-85ed-29154791fb3d
-- title:
--   Continuous logarithms on open sets with simply connected components
-- statement:
--   Let $X$ be a locally path-connected topological space, and let $U\subseteq X$ be open with each connected component simply connected. Then every continuous function $F:U\to\mathbb C\setminus\{0\}$ has a continuous logarithm: there exists a continuous $f:U\to\mathbb C$ such that
--
--   $$\exp(f(x))=F(x)\qquad(x\in U).$$
--
--   The open set $U$ is allowed to be disconnected or empty.
-- source:
--   Componentwise consequence of the simply connected case in Mathlib, Complex.exists_continuousOn_eqOn_exp_comp, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/BranchLogRoot.lean ; used in the logarithm obstruction approach to https://prove2.me/theorems/192efa39-8303-4dbe-8d90-22363baaf03f .

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Topology.Connected.LocallyConnected

open Set

theorem continuous_log_on_open_simply_connected_components {X : Type} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (U : Set X) (hU : IsOpen U)
    (hsc : ∀ x ∈ U, IsSimplyConnected (connectedComponentIn U x))
    (F : X → ℂ) (hFc : ContinuousOn F U) (hFne : ∀ x ∈ U, F x ≠ 0) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ EqOn (fun x => Complex.exp (f x)) F U := by sorry
