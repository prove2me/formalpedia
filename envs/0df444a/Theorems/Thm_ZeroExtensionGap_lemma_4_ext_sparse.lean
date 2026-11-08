-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_4_ext_sparse
-- name    : ZeroExtensionGap.lemma_4_ext_sparse
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:35.846538+00:00
-- url     : https://prove2.me/theorems/055aaeac-3b9e-4bbb-bc77-bd77ca7bf475
-- title:
--   Lemma 4 — connected core-sparse sets of $\mathrm{Ext}(Q,H)$ induce few edges
-- statement:
--   Let $H,\gamma,\kappa$ be as in Lemma 2, let $Q$ be a simple graph with at most $n^{t-1}$ vertices and maximum degree at most $10(t-1)$, and let $Y=\mathrm{Ext}(Q,H)$. There is a constant $\kappa'>0$ depending only on $t$ such that, with probability at least $1-2n^{-4}$, every core-sparse set $S\subseteq V(Y)$ such that $Y[S]$ is connected and $|S|\ge\lfloor\gamma\log n\rfloor$ satisfies
--
--   $$|E(Y[S])|\le\Big(1+\frac{\kappa'}{\log n}\Big)|S|.$$
--
--   The bound is simultaneous for all such $S$, and concerns $Y$ before pruning.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 → every admissible choice of these constants (`BaseConstants`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: probability over independent uniform bijections → counting ratio `probUniform` on `ExtSample Q (Fin n)`; reason: the same uniform law on a finite set
--   - encoding: "we fix an ordering of the endpoints" → the choice-based `edgeTail`, `edgeHead`; reason: the uniform law does not see the ordering, since $\varphi\mapsto\varphi^{-1}$ preserves it
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 4, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 4, p.9 (PDF p.11). The probability is over the uniform bijections of `Ext(Q, H)`,
before pruning.
**Formalization Note.** `κ'` is chosen before `n`, `H` and `Q`, from `t` and the constants of Lemma 2.
`n` sufficiently large and even is standing (§3, p.7, PDF p.9). The condition on `S` is inside the event,
so the bound is simultaneous for all `S`. -/
theorem lemma_4_ext_sparse (t : ℕ) (ht : 1 ≤ t) (h₀ γ κ : ℝ) (hc : BaseConstants t h₀ γ κ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ H : SimpleGraph (Fin n), BaseGraphProps h₀ γ κ H →
      ∀ (A : Type) [Fintype A] (Q : SimpleGraph A),
        Fintype.card A ≤ n ^ (t - 1) → MaxDegreeLE Q (10 * (t - 1)) →
        1 - 2 * (n : ℝ) ^ (-4 : ℝ) ≤ probUniform fun φ : ExtSample Q (Fin n) =>
          ∀ S : Finset (A × Fin n), IsCoreSparse n S →
            ((extGraph Q H φ).induce (S : Set (A × Fin n))).Connected →
            gOf γ n ≤ S.card →
            (inducedEdgeCount (extGraph Q H φ) S : ℝ) ≤
              (1 + κ' / Real.log (n : ℝ)) * (S.card : ℝ) := by sorry

end ZeroExtensionGap
