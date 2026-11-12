-- Prove2me | Theorems.Thm_ZeroOneExpansion_lemma_11
-- name    : ZeroOneExpansion.lemma_11
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:23:14.832652+00:00
-- url     : https://prove2.me/theorems/1c87d8a6-16da-45bd-a584-7d5187c5c6ba
-- title:
--   Lemma 11 — cross-layer edges preserve $I$, $J$; the components $V_{K,L}$
-- statement:
--   Let $n\ge1$.
--
--   1. Every cross-layer edge $uv$ of $P_n$ satisfies $I(u)=I(v)$ and $J(u)=J(v)$.
--   2. For $K,L\subseteq[n]$, the set $V_{K,L}=\{u\in V_n: I(u)=K,\ J(u)=L\}$ is a connected component of the cross-layer graph $(V_n,E_{\mathrm{cross}})$.
--   3. The lower and upper layers of $V_{K,L}$ have cardinalities $3^{|K|}2^{|L|}$ and $2^{|K|}3^{|L|}$, respectively.
--
--   The asymmetry between the two layer sizes is what makes the cut $S_n$ have few boundary edges.
--
--   Differences from the source:
--   - encoding: blocks 1, …, 2n and [n] = {1, …, n} → blocks indexed by Fin n ⊕ Fin n (first group inl, second group inr), [n] as Fin n (0-based); block k at coordinates 2k−2, 2k−1, t last; reason: a relabelling; same instances
--   - encoding: (V_n, E_cross) → crossGraph n on the vertices of P_n: adjacent in G_n and different last coordinate; reason: the vertices of P_n are V_n by Fact 3
--   - encoding: "V_{K,L} is a connected component" → some connected component of crossGraph n has support exactly V_{K,L}; reason: the definition of a connected component as a vertex set
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Lemma 11, p.7

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_crossGraph

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Lemma 11** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.7). Every cross-layer edge `uv` satisfies `I(u) = I(v)` and
`J(u) = J(v)`. Moreover, for `K, L ⊆ [n]`, `V_{K,L} := {u ∈ Vn : I(u) = K, J(u) = L}` is a connected
component of `(Vn, Ecross)`, and its lower and upper layers have cardinalities `3^{|K|} 2^{|L|}` and
`2^{|K|} 3^{|L|}`.

**Formalization Note** §3 fixes `n ≥ 1`. `(Vn, Ecross)` is `crossGraph n` on the vertices of `Pn`
(adjacent in `Gn`, different layers). "A connected component" is: there is a connected component of
`crossGraph n` whose support is exactly `V_{K,L}`. The lower layer is `t = 0`, the upper `t = 1`.
Cardinalities are `Set.ncard`. -/
theorem lemma_11 (n : ℕ) (hn : 1 ≤ n) :
    (∀ u v : Grunbaum2003.PolytopeVertex (Pn n), (crossGraph n).Adj u v →
        Iset n u.val = Iset n v.val ∧ Jset n u.val = Jset n v.val) ∧
    ∀ K L : Finset (Fin n),
      (∃ CC : (crossGraph n).ConnectedComponent,
          CC.supp = {u | Iset n u.val = K ∧ Jset n u.val = L}) ∧
      {u : Grunbaum2003.PolytopeVertex (Pn n) |
          Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 0}.ncard =
        3 ^ K.card * 2 ^ L.card ∧
      {u : Grunbaum2003.PolytopeVertex (Pn n) |
          Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 1}.ncard =
        2 ^ K.card * 3 ^ L.card := by sorry

end ZeroOneExpansion
