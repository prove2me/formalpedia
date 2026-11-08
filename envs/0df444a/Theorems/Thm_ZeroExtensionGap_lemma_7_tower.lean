-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_7_tower
-- name    : ZeroExtensionGap.lemma_7_tower
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:05.47603+00:00
-- url     : https://prove2.me/theorems/9ae6f508-1cd9-4fe7-b210-ede910e40d81
-- title:
--   Lemma 7 — existence of a valid expander tower
-- statement:
--   There are a constant $\kappa_{\mathrm{tow}}>0$ depending only on $t$ and an expander tower $X_t,\dots,X_1$ with base graph $H$ such that:
--
--   1. for every $i\in[t]$, $X_i$ is simple and connected, has $n^{t-i+1}$ vertices, maximum degree at most $10(t-i+1)$ and girth at least $g=\lfloor\gamma\log n\rfloor$;
--   2. for every $i\in[t-1]$, each outer matching used to construct $X_i$ from $X_{i+1}$ retains at least $n-\lceil n^{0.99}\rceil$ edges after pruning;
--   3. for every $i\in[t]$ and every core-sparse $S\subseteq V(X_i)$, $\Gamma(X_i[S])\le1+\kappa_{\mathrm{tow}}/\log n$.
--
--   Core-sparsity is with respect to the cores of $X_i$, and $X_t=H$ is its own sole core. A tower with these properties is called valid.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 → every admissible choice of these constants (`BaseConstants`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: stage $X_i$ with vertex tuples $(x_t,\dots,x_i)$ → depth $j=t-i$, `towerGraph H g φ j` on the nested product `TowerV n j`; reason: a reindexing of the same tower
--   - encoding: "we fix an ordering of the endpoints" → the choice-based `edgeTail`, `edgeHead`; reason: the uniform law does not see the ordering, since $\varphi\mapsto\varphi^{-1}$ preserves it
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 7, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 7, p.16 (PDF p.18).
**Formalization Note.** An expander tower with base graph `H` is `towerGraph H (gOf γ n) φ`, so "there
exists a tower" is the existence of realizations `φ`. `TowerProps` is clauses 1–3, with depth `j = t - i`.
`κtow` is chosen from `t` and the constants of Lemma 2, before `n` and `H`. -/
theorem lemma_7_tower (t : ℕ) (ht : 1 ≤ t) (h₀ γ κ : ℝ) (hc : BaseConstants t h₀ γ κ) :
    ∃ κtow : ℝ, 0 < κtow ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ H : SimpleGraph (Fin n), BaseGraphProps h₀ γ κ H →
        ∃ φ : Realization n, TowerProps t γ κtow H φ := by sorry

end ZeroExtensionGap
