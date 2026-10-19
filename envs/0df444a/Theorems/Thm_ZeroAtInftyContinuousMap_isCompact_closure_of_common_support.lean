-- Prove2me | Theorems.Thm_ZeroAtInftyContinuousMap_isCompact_closure_of_common_support
-- name    : ZeroAtInftyContinuousMap.isCompact_closure_of_common_support
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T17:01:51.780647+00:00
-- url     : https://prove2.me/theorems/1b4bdf3a-3d0b-45a6-b0e4-61a6be10270d
-- title:
--   Arzela–Ascoli in C0 for a family with common compact support
-- statement:
--   Let $X$ be a topological space and $\mathcal A\subseteq C_0(X,\mathbb R)$. Suppose that there is a compact subset $K\subseteq X$ such that every $u\in\mathcal A$ vanishes outside $K$, that $|u(x)|\le M$ for all $u\in\mathcal A$ and $x\in X$, and that $\mathcal A$ is equicontinuous. Then
--   $$\overline{\mathcal A}\text{ is compact in }C_0(X,\mathbb R)$$
--   for the supremum norm.
--
--   This common-support form of Arzela–Ascoli allows compactness on a compact domain to be used for functions on a noncompact ambient space. Empty families and empty supports are included; no separation or local compactness assumption on $X$ is needed.
-- source:
--   Common-support corollary of Arzela–Ascoli: Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli, theorem BoundedContinuousFunction.arzela_ascoli, Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean; application in Hunter, Notes on PDEs (2014), p.75, proof of Theorem 3.48

import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

open Set
open scoped ZeroAtInfty BoundedContinuousFunction Topology

theorem ZeroAtInftyContinuousMap.isCompact_closure_of_common_support {X : Type*} [TopologicalSpace X]
    (A : Set C₀(X, ℝ)) (K : Set X) (hK : IsCompact K)
    (hsupp : ∀ u ∈ A, ∀ x ∉ K, u x = 0)
    (M : ℝ) (hM : ∀ u ∈ A, ∀ x, |u x| ≤ M)
    (heq : Equicontinuous (fun u : A => (u.1 : X → ℝ))) :
    IsCompact (closure A) := by sorry
