-- Prove2me | Theorems.Thm_ZeroOneExpansion_lemma_13
-- name    : ZeroOneExpansion.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:16.827204+00:00
-- url     : https://prove2.me/theorems/16388757-4c06-49f1-863a-7fe11a9f3940
-- title:
--   Lemma 13 — $|\delta_{G_n}(S_n)|=\sum_r A_{r,r}(4(n-r)+5r/3)\le4n\sum_rA_{r,r}$
-- statement:
--   For every $n\ge1$, the edge boundary of $S_n$ in $G_n$ satisfies
--   $$|\delta_{G_n}(S_n)|=\sum_{r=0}^nA_{r,r}\Big(4(n-r)+\frac{5r}{3}\Big)\le 4n\sum_{r=0}^nA_{r,r}.$$
--
--   Combined with Lemma 12 this bounds the ratio $|\delta_{G_n}(S_n)|/|S_n|$.
--
--   Differences from the source:
--   - encoding: |δ_{G_n}(S_n)|, edges with one endpoint in S_n → ncard of the ordered pairs (u, v), u ∈ S_n, v ∉ S_n, adjacent; reason: each boundary edge is counted once
--   - encoding: the identity with 5r/3 → both clauses in ℝ; reason: 5r/3 is not an integer in general
--   - encoding: S_n ⊆ V_n, with I(u), J(u) over [n] → Sn n, a set of vertices of P_n (Grunbaum2003.PolytopeVertex (Pn n)), with I, J as Iset/Jset over Fin n (0-based); reason: the vertices of P_n are V_n (Fact 3); [n] relabelled 0-based; same instances
--   - encoding: G_n = (V_n, E_n), the 1-skeleton of P_n → Gn n = Grunbaum2003.polytopeGraph (Pn n); reason: distinct vertices in a common one-dimensional exposed face, the paper's G(P)
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Lemma 13, display (3), p.8

import Mathlib
import Definitions.Def_ZeroOneExpansion_Sn
import Definitions.Def_ZeroOneExpansion_edgeExpansion

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Lemma 13** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.8, display (3)). For every `n ≥ 1`,
`|δ_{Gn}(Sn)| = ∑_{r=0}^n A_{r,r} (4(n − r) + 5r/3) ≤ 4n ∑_{r=0}^n A_{r,r}`.

**Formalization Note** `|δ_{Gn}(Sn)|` is `Set.ncard (edgeBoundary (Gn n) (Sn n))`: each boundary
edge counted once, as the ordered pair oriented out of `Sn`, the same convention as `edgeExpansion`.
Both the identity and the bound are in `ℝ` (`5r/3` is not an integer in general). -/
theorem lemma_13 (n : ℕ) (hn : 1 ≤ n) :
    ((edgeBoundary (Gn n) (Sn n)).ncard : ℝ) =
        ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ) * (4 * ((n : ℝ) - r) + 5 * (r : ℝ) / 3) ∧
    ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ) * (4 * ((n : ℝ) - r) + 5 * (r : ℝ) / 3) ≤
        4 * n * ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ) := by sorry

end ZeroOneExpansion
