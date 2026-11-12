-- Prove2me | Theorems.Thm_ZeroOneExpansion_fact_5
-- name    : ZeroOneExpansion.fact_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:21:16.37464+00:00
-- url     : https://prove2.me/theorems/135be57e-ee6b-4ada-ad2f-c77a92275179
-- title:
--   Fact 5 — faces, vertices and edges of a product of polytopes
-- statement:
--   Let $n\ge1$ and let $P_i\subseteq\mathbb R^{d_i}$ be polytopes for $i\in[n]$; write $P=P_1\times\cdots\times P_n$.
--
--   1. For every $c=(c_1,\dots,c_n)$ with $c_i\in\mathbb R^{d_i}$, $$F_c(P)=F_{c_1}(P_1)\times\cdots\times F_{c_n}(P_n).$$
--   2. $V(P)=V(P_1)\times\cdots\times V(P_n)$.
--   3. Two distinct vertices $x=(x_1,\dots,x_n)$ and $y=(y_1,\dots,y_n)$ of $P$ are adjacent if and only if, for some $j\in[n]$, $x_i=y_i$ for all $i\neq j$ and $x_j,y_j$ are adjacent in $P_j$.
--
--   Equivalently, $G(P)$ is the Cartesian product of $G(P_1),\dots,G(P_n)$. This is how the same-layer edges of $P_n$ are found (Lemma 8).
--
--   Differences from the source:
--   - encoding: F_c(P) = {x ∈ P : c·x = max_{y∈P} c·y} → the maximizer set {x ∈ P | ∀ y ∈ P, c·y ≤ c·x} (exposedFace); reason: equal whenever the maximum exists, as on every polytope
--   - encoding: P ⊆ ℝ^{d_1} × ⋯ × ℝ^{d_n}, c·x = Σ c_i·x_i → Set.univ.pi P ⊆ Π i, (Fin (d i) → ℝ), functional x ↦ Σ i, c i ⬝ᵥ x i; reason: the same space and functional
--   - encoding: vertices and adjacency in P and P_i → the local IsVertexOf / IsAdj over a general real topological vector space; reason: on ℝ^d they agree with Grunbaum2003.PolytopeVertex / polytopeGraph (proved in the verification file)
--   - reading: "Equivalently, G(P) is the Cartesian product of G(P_1), …, G(P_n)" → not stated as a separate graph isomorphism; it is clauses 2 and 3 (vertex set and adjacency); reason: the paper presents it as a restatement of the adjacency clause
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Fact 5, p.4

import Mathlib
import Definitions.Def_ZeroOneExpansion_IsPolytope
import Definitions.Def_ZeroOneExpansion_exposedFace
import Definitions.Def_ZeroOneExpansion_IsAdj

set_option autoImplicit false

open Matrix

namespace ZeroOneExpansion

/-- **Fact 5** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.4). Let `n ≥ 1` and let `P_i ⊆ ℝ^{d_i}` be polytopes, `P = P_1 × ⋯ × P_n`.
1. For `c = (c_1, …, c_n)`, `F_c(P) = F_{c_1}(P_1) × ⋯ × F_{c_n}(P_n)`.
2. `V(P) = V(P_1) × ⋯ × V(P_n)`.
3. Two distinct vertices `x, y` of `P` are adjacent iff for some `j`, `x_i = y_i` for all `i ≠ j` and
   `x_j, y_j` are adjacent in `P_j`.

**Formalization Note** The product is `Set.univ.pi P ⊆ Π i, (Fin (d i) → ℝ)` and
`c · x = ∑ i, c_i · x_i`. Vertices and adjacency are the local `IsVertexOf`/`IsAdj` (exposed
singleton; distinct vertices in a common exposed face of affine dimension one), the general-space
form of `Grunbaum2003.PolytopeVertex`/`polytopeGraph`. The paper's restatement "G(P) is the
Cartesian product of G(P_1), …, G(P_n)" is clause 3 (adjacency) together with clause 2 (vertex set). -/
theorem fact_5 (n : ℕ) (hn : 1 ≤ n) (d : Fin n → ℕ) (P : (i : Fin n) → Set (Fin (d i) → ℝ))
    (hP : ∀ i, IsPolytope (P i)) :
    (∀ c : (i : Fin n) → Fin (d i) → ℝ,
      exposedFace (Set.univ.pi P) (fun x => ∑ i, c i ⬝ᵥ x i) =
        Set.univ.pi fun i => exposedFace (P i) (fun y => c i ⬝ᵥ y)) ∧
    {x | IsVertexOf (Set.univ.pi P) x} = Set.univ.pi (fun i => {y | IsVertexOf (P i) y}) ∧
    ∀ x y : (i : Fin n) → Fin (d i) → ℝ,
      IsVertexOf (Set.univ.pi P) x → IsVertexOf (Set.univ.pi P) y → x ≠ y →
        (IsAdj (Set.univ.pi P) x y ↔
          ∃ j : Fin n, (∀ i, i ≠ j → x i = y i) ∧ IsAdj (P j) (x j) (y j)) := by sorry

end ZeroOneExpansion
