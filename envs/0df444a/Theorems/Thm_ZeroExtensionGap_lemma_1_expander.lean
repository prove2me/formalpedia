-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_1_expander
-- name    : ZeroExtensionGap.lemma_1_expander
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:02.87027+00:00
-- url     : https://prove2.me/theorems/80fbe6ff-9990-4e36-a330-e80faf63f16e
-- title:
--   Lemma 1 ([ABL02, ALN+06, CMM10], cited) — $3$-regular expanders of logarithmic girth with locally sparse small sets
-- statement:
--   There are constants $0<h_0\le1$, $\gamma^*>0$ and $a>0$ such that, for every sufficiently large even integer $n$ and every integer $k\in[n-1]$, there is a simple $3$-regular graph $H$ on $n$ vertices with edge expansion at least $h_0$ and girth at least $\gamma^*\log n$, satisfying
--
--   $$|E(H[S])|\le\Big(1+\frac{a}{\log(n/k)}\Big)|S|$$
--
--   for every $S\subseteq V(H)$ with $|S|\le k$.
--
--   This is the starting point of the construction. It is a cited result, and the paper gives no proof and no theorem number from those sources. Lemma 2 applies it with $k=\lfloor n^{0.9}\rfloor$.
--
--   Differences from the source:
--   - encoding: a graph $H$ on $n$ vertices → `SimpleGraph (Fin n)`; reason: every $n$-element vertex set is a copy of `Fin n`
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 1 ([ABL02, ALN+06, CMM10]), p.6 (PDF p.8). A cited result: the paper gives no proof
and no theorem number from those sources.
**Formalization Note.** The three constants come before `n` and `k`, and `H` may depend on `k`, as
the printed order allows. `k ∈ [n − 1]` is `1 ≤ k ≤ n - 1`, so `n / k > 1` and the logarithm is positive. -/
theorem lemma_1_expander :
    ∃ h₀ γs a : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < γs ∧ 0 < a ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → ∃ H : SimpleGraph (Fin n),
        (∀ v, vdeg H v = 3) ∧ EdgeExpansionAtLeast H h₀ ∧
        GirthAtLeast H (γs * Real.log (n : ℝ)) ∧
        ∀ S : Finset (Fin n), S.card ≤ k →
          (inducedEdgeCount H S : ℝ) ≤
            (1 + a / Real.log ((n : ℝ) / (k : ℝ))) * (S.card : ℝ) := by sorry

end ZeroExtensionGap
