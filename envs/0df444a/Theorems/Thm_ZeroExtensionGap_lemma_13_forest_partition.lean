-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_13_forest_partition
-- name    : ZeroExtensionGap.lemma_13_forest_partition
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:10.263876+00:00
-- url     : https://prove2.me/theorems/3becc631-cc7c-4a65-8d93-c8bf42235ed2
-- title:
--   Lemma 13 — random partitions from small fractional arboricity
-- statement:
--   Let $\theta\ge0$, and let $G=(V,E)$ be a graph without self-loops with $\Gamma(G)\le1+\theta$ and edge lengths at least $a>0$. For every $\Lambda>0$ there is a $\Lambda$-bounded random partition $P$ of $V$ such that
--
--   $$\Pr[P(x)\ne P(y)]\le\Big(\frac2\Lambda+\frac\theta a\Big)d_G(x,y)$$
--
--   for every $x,y\in V$ connected in $G$.
--
--   Differences from the source:
--   - encoding: a finite graph, possibly with parallel edges → `ends : E → Sym2 V` on finite types; reason: the standard presentation of a multigraph; §2 calls a graph simple only when it has neither loops nor parallel edges
--   - encoding: a random partition → its law, `PMF (Finpartition _)`; reason: partitions of a finite set form a finite type, whatever process generated them
--   - encoding: shortest-path distance $d$ with values in $[0,\infty]$ → `ℝ≥0∞`, with `toReal` under connectivity; reason: on connected pairs the real value is the distance; there is no junk value
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 13, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ZeroExtensionGap_MGraph
import Definitions.Def_ZeroExtensionGap_RandomPartition

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 13, p.22 (PDF p.24), on a finite multigraph without self-loops (a "graph" may have
parallel edges, §2, p.5, PDF p.7).
**Formalization Note.** The bound is only for connected `x, y`, as printed; there `mdist` is finite and its
real value is the distance. `θ = 0` is allowed. -/
theorem lemma_13_forest_partition {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (θ : ℝ) (hθ : 0 ≤ θ)
    (hΓ : mFracArb ends ≤ 1 + θ) (ℓ : E → ℝ) (a : ℝ) (ha : 0 < a) (hℓ : ∀ e, a ≤ ℓ e)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ P : PMF (Finpartition (Finset.univ : Finset V)),
      IsBoundedRandomPartition (mdist ends ℓ) Λ P ∧
      ∀ x y : V, MConnected ends x y →
        separationProb P x y ≤ (2 / Λ + θ / a) * (mdist ends ℓ x y).toReal := by sorry

end ZeroExtensionGap
