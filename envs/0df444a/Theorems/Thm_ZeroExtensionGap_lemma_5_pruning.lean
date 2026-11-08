-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_5_pruning
-- name    : ZeroExtensionGap.lemma_5_pruning
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:44.665472+00:00
-- url     : https://prove2.me/theorems/cac25380-e4e9-4eb0-a26f-3a45ba4f2e9c
-- title:
--   Lemma 5 — pruning deletes few edges from each outer matching
-- statement:
--   Let $Q$ be a simple graph with at most $n^{t-1}$ vertices and maximum degree at most $10(t-1)$, let $Y:=\mathrm{Ext}(Q,H)$ and let $\widehat Y:=\widehat{\mathrm{Ext}}(Q,H)$ be its pruned extension with threshold $\lfloor\gamma\log n\rfloor$. Then
--
--   $$\Pr\big[|M\setminus E(\widehat Y)|\le\lceil n^{0.99}\rceil\text{ for every outer matching }M\text{ of }Y\big]\ge1-\frac1n.$$
--
--   Here $H$ is the $n$-vertex expander of Lemma 2, fixed on p.11. There is one outer matching per edge of $Q$.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 → every admissible choice of these constants (`BaseConstants`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: probability over independent uniform bijections → counting ratio `probUniform` on `ExtSample Q (Fin n)`; reason: the same uniform law on a finite set
--   - encoding: "we fix an ordering of the endpoints" → the choice-based `edgeTail`, `edgeHead`; reason: the uniform law does not see the ordering, since $\varphi\mapsto\varphi^{-1}$ preserves it
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 5, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 5, p.12 (PDF p.14). The event is simultaneous over all outer matchings, one for each
edge of `Q`, and `|M \ E(Ŷ)|` is `deletedCount`.
**Formalization Note.** `H` is the `n`-vertex expander fixed on p.11 (PDF p.13), with the constants of
Lemma 2, and `g = ⌊γ log n⌋`. `n` sufficiently large and even is standing. -/
theorem lemma_5_pruning (t : ℕ) (ht : 1 ≤ t) (h₀ γ κ : ℝ) (hc : BaseConstants t h₀ γ κ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ H : SimpleGraph (Fin n), BaseGraphProps h₀ γ κ H →
      ∀ (A : Type) [Fintype A] (Q : SimpleGraph A),
        Fintype.card A ≤ n ^ (t - 1) → MaxDegreeLE Q (10 * (t - 1)) →
        1 - 1 / (n : ℝ) ≤ probUniform fun φ : ExtSample Q (Fin n) =>
          ∀ e : Q.edgeSet,
            deletedCount (prunedExt Q H (gOf γ n) φ) (outerMatching Q φ e) ≤
              ⌈(n : ℝ) ^ (0.99 : ℝ)⌉₊ := by sorry

end ZeroExtensionGap
