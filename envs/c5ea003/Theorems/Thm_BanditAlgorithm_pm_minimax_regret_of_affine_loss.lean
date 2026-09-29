-- Prove2me | Theorems.Thm_BanditAlgorithm_pm_minimax_regret_of_affine_loss
-- name    : BanditAlgorithm.pm_minimax_regret_of_affine_loss
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T16:30:21.306414+00:00
-- url     : https://prove2.me/theorems/e20801e5-a52c-4361-8ced-c46079bd9ad2
-- title:
--   Minimax regret under an affine change of the loss matrix
-- statement:
--   Minimax regret in partial monitoring is unchanged by shifting the loss matrix along outcomes, and scales linearly when the losses are rescaled.
--
--   Let $G=(L,\Phi)$ and $G'=(L',\Phi)$ be partial monitoring games with the *same* feedback matrix, whose loss matrices are related by
--
--   $$
--   L'_{a,i} \;=\; \lambda\, L_{a,i} + c_i, \qquad \lambda\ge 0,
--   $$
--
--   where the shift $c_i$ may depend on the outcome $i$ but not on the action $a$. Then for every horizon $n$,
--
--   $$
--   R^*_n(G') \;=\; \lambda\, R^*_n(G).
--   $$
--
--   The reason is that regret is defined through loss *differences* $L_{A_t,i_t}-L_{a,i_t}$: the shift $c_{i_t}$ appears in both terms and cancels identically, while $\lambda$ factors out of the sum, the integral, the supremum over comparator actions, the supremum over outcome sequences and the infimum over policies.
--
--   This is the normalisation step that lets results proved for games with losses in $[0,1]$ be applied to a game with an arbitrary real loss matrix: since a loss matrix is finite, it can always be brought into $[0,1]$ by such an affine map, and any constants in the conclusion simply rescale.
--
--   **Formalization Note** The interaction measure depends on the game only through the feedback matrix $\Phi$, never through $L$ — the learner observes signals, not losses — so the two games induce literally the same law over histories, which is what makes the comparison exact rather than merely asymptotic. Nonnegativity of $\lambda$ is needed: for $\lambda<0$ the suprema and infima would exchange.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : the regret of a partial monitoring game, Section 37.2, printed p. 483, is defined through loss differences; the normalisation is what connects Theorems 37.15-37.17 (printed pp. 494-500, stated for losses in [0,1]) to the classification Theorem 37.11 (printed p. 487), which quantifies over an arbitrary real loss matrix.

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.pm_minimax_regret_of_affine_loss {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G G' : PartialMonitoringGame k d 𝕊)
    (lam : ℝ) (hlam : 0 ≤ lam) (c : Fin d → ℝ)
    (hL : ∀ a i, G'.L a i = lam * G.L a i + c i) (hΦ : G'.Φ = G.Φ) (n : ℕ) :
    pmMinimaxRegret G' n = lam * pmMinimaxRegret G n := by
  sorry
