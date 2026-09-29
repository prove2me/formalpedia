-- Prove2me | Theorems.Thm_KServer_tree_swap_first_two
-- name    : KServer.tree_swap_first_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T07:05:05.578721+00:00
-- url     : https://prove2.me/theorems/52f00ccc-2db8-4b37-ac53-c54cbc7d7b1c
-- title:
--   CK 2021, Lemma 25 — a swap-symmetric minimizing anchor triple with resolution to the first anchor
-- statement:
--   **Lemma 25 of Coester and Koutsoupias, for three servers on trees.** Let $M$ be the vertex set of a finite weighted tree with distances bounded by $\Delta$, and let $\Phi$ be the Coester--Koutsoupias potential of a $3$-server instance --- the minimum over anchor triples $x_1, x_2, x_3 \in M$ of the anchored sum $\Phi_{x_1x_2x_3}(w) = w(x_1x_2x_3) + w(\bar x_1x_2x_3) + w(\bar x_2\bar x_2 x_3) + w(\bar x_3^3)$, the work function evaluated in the antipodal extension. Then a minimising triple can be chosen with two additional properties:
--
--   $$\Phi(w) = \Phi_{x_1x_2x_3}(w) = \Phi_{x_2x_1x_3}(w), \qquad w(\bar x_2 \bar x_2 x_3) = w(\bar x_2\, x_1\, x_3) + d(x_1, \bar x_2).$$
--
--   The triple is **symmetric in its first two anchors**, and the doubled antipode of the second anchor **resolves to the first anchor**.
--
--   ## Role
--
--   This is the normalisation device of the tree analysis: in the case analysis of Theorem 23, whenever a resolution statement is available for one of the first two anchors, the swap-symmetry converts it to the other, and the resolution of $\bar x_2 \bar x_2 x_3$ to $x_1$ is the hypothesis of the anchor-exchange inequality. Both properties come from *choosing* the first anchor greedily rather than merely minimising.
--
--   ## Structure of the proof
--
--   Fix a minimising triple $(y_1, x_2, x_3)$ and re-choose the first anchor as $x_1 \in \arg\min_u \bigl( w(u\,x_2 x_3) - d(x_2, u) \bigr)$ (the anchor space is finite). Three facts then combine:
--
--   1. **$(x_1, x_2, x_3)$ still minimises.** The $x_1$-dependent part of the anchored potential is the one-server potential of the restriction $u \mapsto w(u\,x_2x_3)$: by the coordinate-local envelope, $w(\bar t\, x_2 x_3) = \min_u (w(u\,x_2x_3) + 2\Delta - d(u,t))$. The one-server anchor lemma for trees --- any minimiser of $w(u) - d(c,u)$ realises the one-server potential, an instance of the four-point condition --- applied with reference point $c = x_2$ shows the greedy $x_1$ does at least as well as $y_1$.
--
--   2. **Resolution to $x_1$.** By the two-coordinate envelope, $w(\bar x_2\bar x_2 x_3)$ is $4\Delta$ plus the global minimum of the dual pair functional $F(u,v) = w(x_3uv) - d(u,x_2) - d(v,x_2)$; the greedy exchange for $F$ puts $x_1$ inside a global minimiser $(x_1, w')$; and two Lipschitz collapses ($w' \to \bar x_2$, then comparison with the direct move $x_1 \to \bar x_2$) turn this into the resolution identity, which holds with equality.
--
--   3. **Swap symmetry.** The resolution identity is precisely the hypothesis of the anchor-swap inequality $\Phi_{x_2x_1x_3} \le \Phi_{x_1x_2x_3}$, and minimality of the triple gives the reverse.
--
--   ## Formalization note
--
--   `ckPot`/`ckPotAt` are the potential and its anchored form; anchors range over the base space, antipodes are `Sum.inr` in the extension `antipodalExtension` on $M \oplus M$, and $d(x_1, \bar x_2) = 2\Delta - d(x_1,x_2)$ is literal. The statement is for an arbitrary request sequence: no last-request structure is needed.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section Trees, Lemma 25 (lem:treeSwapx12), case k = 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_tree_metric
import Definitions.Def_KServer_ck_potential

namespace KServer

theorem tree_swap_first_two (M : Type) [MetricSpace M] [Fintype M] [Nonempty M]
    (hM : IsTreeVertexSpace M) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) :
    ∃ x₁ x₂ x₃ : M,
      ckPot M Δ hΔ0 hΔ C₀ σ = ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃
      ∧ ckPotAt M Δ hΔ0 hΔ C₀ σ x₂ x₁ x₃ = ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃
      ∧ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
          + (2 * Δ - dist x₁ x₂) := by sorry

end KServer
