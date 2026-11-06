-- Prove2me | Theorems.Thm_ZeroOneExpansion_lemma_8
-- name    : ZeroOneExpansion.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:34.840118+00:00
-- url     : https://prove2.me/theorems/87d7e8a5-34a6-4d6d-8afd-43cdff5f4e91
-- title:
--   Lemma 8 — same-layer edges of $P_n$
-- statement:
--   Let $n\ge1$ and let $u=(u_1,\dots,u_{2n};t)$ and $v=(v_1,\dots,v_{2n};t)$ be distinct vertices of $P_n$ in the same layer. Then $[u,v]$ is an edge of $P_n$ if and only if $u$ and $v$ differ in exactly one block $k$, and $u_k$, $v_k$ are adjacent in the $k$-th factor of
--
--   1. $Q^n\times\Delta^n$ when $t=0$ (the factor is $Q$ for $k\le n$ and $\Delta$ for $k>n$);
--   2. $\Delta^n\times Q^n$ when $t=1$ (the factor is $\Delta$ for $k\le n$ and $Q$ for $k>n$).
--
--   Here $Q=[0,1]^2$ and $\Delta$ is the standard 2-simplex. Together with Corollary 10 this determines the graph $G_n$.
--
--   Differences from the source:
--   - encoding: "[u, v] is an edge" (a one-dimensional face) → the segment [u, v] is a face (IsExposed ℝ P (segment ℝ u v)); reason: the two endpoints are distinct, so the segment is one-dimensional, and a one-dimensional face is an edge
--   - encoding: blocks 1, …, 2n and [n] = {1, …, n} → blocks indexed by Fin n ⊕ Fin n (first group inl, second group inr), [n] as Fin n (0-based); block k at coordinates 2k−2, 2k−1, t last; reason: a relabelling; same instances
--   - reading: "u and v differ in exactly one block, say k" → ∃ k, all blocks other than k agree, and u_k, v_k are adjacent in the factor (so u_k ≠ v_k); reason: adjacency of u_k, v_k forces them to differ, so this is exactly "differ in block k only"
--   - encoding: adjacent in the k-th factor Q or ∆ → IsAdj Qsq / IsAdj Delta on ℝ²; reason: the paper's adjacency (distinct vertices in a common one-dimensional face)
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Lemma 8, p.5

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_IsAdj

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Lemma 8** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.5). Let `u = (u_1, …, u_{2n}; t)` and `v = (v_1, …, v_{2n}; t)` be distinct
vertices of `Pn`. Then `[u, v]` is an edge of `Pn` iff `u` and `v` differ in exactly one block `k`,
and `u_k`, `v_k` are adjacent in the `k`-th factor of `Q^n × ∆^n` when `t = 0`, and of `∆^n × Q^n`
when `t = 1`.

**Formalization Note** §3 fixes `n ≥ 1`. Blocks are indexed by `Fin n ⊕ Fin n` (first group
`Sum.inl i`, second group `Sum.inr j`); `ublk n u k` is the block `u_k ∈ ℝ^2` and `layer n u` is
`t`. "`[u, v]` is an edge" is `IsExposed ℝ (Pn n) (segment ℝ u v)` (the segment of two distinct
points is one-dimensional, so it is an edge iff it is a face). Adjacency in the factor `Q = [0,1]^2`
or `∆` is the local `IsAdj` (distinct vertices in a common exposed face of affine dimension one).
"Differ in exactly one block, say `k`" is: all blocks other than `k` agree, and `u_k ≠ v_k`, which
`IsAdj` contains. -/
theorem lemma_8 (n : ℕ) (hn : 1 ≤ n) (u v : Fin (4 * n + 1) → ℝ)
    (hu : IsVertexOf (Pn n) u) (hv : IsVertexOf (Pn n) v) (huv : u ≠ v)
    (ht : layer n u = layer n v) :
    (layer n u = 0 →
      (IsExposed ℝ (Pn n) (segment ℝ u v) ↔
        ∃ k : Fin n ⊕ Fin n, (∀ k', k' ≠ k → ublk n u k' = ublk n v k') ∧
          IsAdj (Sum.elim (fun _ : Fin n => Qsq) (fun _ : Fin n => Delta) k)
            (ublk n u k) (ublk n v k))) ∧
    (layer n u = 1 →
      (IsExposed ℝ (Pn n) (segment ℝ u v) ↔
        ∃ k : Fin n ⊕ Fin n, (∀ k', k' ≠ k → ublk n u k' = ublk n v k') ∧
          IsAdj (Sum.elim (fun _ : Fin n => Delta) (fun _ : Fin n => Qsq) k)
            (ublk n u k) (ublk n v k))) := by sorry

end ZeroOneExpansion
