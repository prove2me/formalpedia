-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_15_extend_partition
-- name    : ZeroExtensionGap.lemma_15_extend_partition
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:28.174788+00:00
-- url     : https://prove2.me/theorems/9fa16616-009e-4c37-b935-170d22798f72
-- title:
--   Lemma 15 — extending a partition through a forest
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $G=(V,E)$ be a graph with positive edge lengths, and let $A\subseteq V$ be such that $F:=(V,E\setminus E(G[A]))$ is a forest. Let $\Lambda>0$ and $\beta\ge0$. Suppose $A$ has a $\Lambda/2$-bounded random partition $P_A$, with respect to $d_G$, satisfying $\Pr[P_A(u)\ne P_A(v)]\le\beta\,d_G(u,v)/\Lambda$ for every $u,v\in A$ connected in $G$. Then there is a $\Lambda$-bounded random partition $P$ of $V$ whose restriction to $A$ is $P_A$ and such that
--
--   $$\Pr[P(x)\ne P(y)]\le c\max\{8,\beta\}\frac{d_G(x,y)}{\Lambda}$$
--
--   for every $x,y\in V$ connected in $G$.
--
--   Differences from the source:
--   - encoding: a finite graph, possibly with parallel edges → `ends : E → Sym2 V` on finite types; reason: the standard presentation of a multigraph; §2 calls a graph simple only when it has neither loops nor parallel edges
--   - encoding: a random partition → its law, `PMF (Finpartition _)`; reason: partitions of a finite set form a finite type, whatever process generated them
--   - encoding: shortest-path distance $d$ with values in $[0,\infty]$ → `ℝ≥0∞`, with `toReal` under connectivity; reason: on connected pairs the real value is the distance; there is no junk value
--   - encoding: the restriction of $P$ to $A$ is $P_A$ → `P.map (restrictPartition A) = PA`; reason: the printed proof builds $P$ from a sample of $P_A$, so the restriction has that law; empty parts are discarded (p.21)
--   - encoding: an absolute constant before all graphs → `∃ c` before `∀ (V E : Type)`; reason: Lean needs a universe to quantify; every finite set has a copy in `Type`
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 15, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_ZeroExtensionGap_MGraph
import Definitions.Def_ZeroExtensionGap_RandomPartition

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 15, p.24 (PDF p.26), on a finite multigraph; `c` is absolute, so it precedes the graph.
**Formalization Note.** `F = (V, E \ E(G[A]))` is the set of edges without both ends in `A`. "Whose restriction
to `A` is `P_A`" is the equality of laws `P.map (restrictPartition A) = PA`, empty parts being discarded (p.21,
PDF p.23). The types live in `Type`, so that `c` can precede them. -/
theorem lemma_15_extend_partition :
    ∃ c : ℝ, 0 < c ∧ ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
      (ends : E → Sym2 V) (ℓ : E → ℝ), (∀ e, 0 < ℓ e) →
      ∀ A : Finset V, MIsForest ends {e | ¬ ∀ v ∈ ends e, v ∈ A} →
      ∀ Λ β : ℝ, 0 < Λ → 0 ≤ β →
      ∀ PA : PMF (Finpartition A), IsBoundedRandomPartition (mdist ends ℓ) (Λ / 2) PA →
        (∀ u ∈ A, ∀ v ∈ A, MConnected ends u v →
          separationProb PA u v ≤ β * (mdist ends ℓ u v).toReal / Λ) →
        ∃ P : PMF (Finpartition (Finset.univ : Finset V)),
          IsBoundedRandomPartition (mdist ends ℓ) Λ P ∧
          P.map (restrictPartition A) = PA ∧
          ∀ x y : V, MConnected ends x y →
            separationProb P x y ≤ c * max 8 β * (mdist ends ℓ x y).toReal / Λ := by sorry

end ZeroExtensionGap
