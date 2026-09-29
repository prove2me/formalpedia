-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_collapsed_bandit_regret_arithmetic
-- name    : BanditAlgorithm.jao_collapsed_bandit_regret_arithmetic
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T17:32:44.965863+00:00
-- url     : https://prove2.me/theorems/ebc3a70f-88e5-4fe4-8399-4e47d9021a5e
-- title:
--   JAO Section 6, final computation: averaging over the planting and the choice $\varepsilon = \frac15\sqrt{\delta m / T}$ leave regret $\ge \frac{1}{100}\sqrt{D' m T}$
-- statement:
--   **Statement.** Let $m \ge 20$, $0 < \delta \le \tfrac13$ and $T$ with $16m \le \delta T$, and set
--   $$\varepsilon \;:=\; \tfrac15\sqrt{\tfrac{\delta m}{T}}.$$
--   Let $V, R : \{1,\dots,m\} \to \mathbb{R}$ satisfy $V_b \ge 0$, $\sum_b V_b \le \tfrac{T}{2} + \tfrac{1}{2\delta}$ and
--   $$R_b \;\ge\; T\cdot\frac{\delta+\varepsilon}{2\delta+\varepsilon} - T + \Bigl(\frac{T}{2} - \frac{1}{2\delta}\Bigr) - \frac{\varepsilon}{\delta}\Bigl(V_b + \frac{T}{2}\cdot\frac{\varepsilon}{\sqrt{\delta}}\sqrt{2V_b}\Bigr)$$
--   for every $b$. Then there exists $b$ with $R_b \ge \frac{1}{100}\sqrt{Tm/\delta}$.
--
--   This is the concluding computation of JAO Section 6 (pp. 1584-1586), isolated as a statement about real numbers so that the probabilistic content lives entirely in its siblings. In the intended application $V_b$ is the expected number of plays of action $b$ in state $s_\circ$ under the *reference* gadget, $R_b$ is the expected regret of the gadget planted at $b$, and the hypothesis on $R_b$ is exactly what equations (34), (35), (37) and the optimal-gain computation give; $\tfrac{T}{\delta} = D'\!\cdot\!T$, so the conclusion is the $\Omega(\sqrt{D' m T})$ of the paper with $m = kA'$.
--
--   **Proof.** Average the hypothesis over $b$. The leading term is $T\bigl(\frac{\delta+\varepsilon}{2\delta+\varepsilon} - \frac12\bigr) = \frac{\varepsilon T}{4\delta + 2\varepsilon}$. Concavity of the square root (Jensen) gives $\frac1m\sum_b \sqrt{2V_b} \le \sqrt{2\bar V}$ with $\bar V = \frac1m\sum_b V_b \le \frac{1}{m}(\frac{T}{2} + \frac{1}{2\delta})$, so the average of the right-hand side is at least
--   $$\frac{\varepsilon T}{4\delta + 2\varepsilon} - \frac{1}{2\delta} - \frac{\varepsilon}{\delta}\bar V - \frac{\varepsilon^2 T}{2\delta^{3/2}}\sqrt{2\bar V}.$$
--   The hypothesis $16m \le \delta T$ gives $\varepsilon \le \delta/20$, hence $4\delta + 2\varepsilon \le (4 + \tfrac18)\delta$, and it makes every correction term a fixed fraction of $\sqrt{Tm/\delta}$; substituting $\varepsilon = \tfrac15\sqrt{\delta m/T}$ and using $m \ge 20$ leaves a positive multiple of $\sqrt{Tm/\delta}$. The extremal case is $m = 20$ with $\delta T = 16m$, where the resulting constant is $0.01748$, comfortably above the $\tfrac{1}{100}$ claimed here (and consistent with the $0.015$ that JAO state for this part of the argument -- it is only their subsequent substitution $D'kA' \to DSA$ that fails). Finally, some $R_b$ attains the average.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the concluding computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2 and its proof in the appendix.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_collapsed_bandit_regret_arithmetic
    (m : ℕ) (hm : 20 ≤ m) (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3)
    (T : ℕ) (hT : (16 : ℝ) * m ≤ δ * T)
    (hε : ε = 1 / 5 * Real.sqrt (δ * m / T))
    (V R : Fin m → ℝ) (hV0 : ∀ b, 0 ≤ V b)
    (hVsum : ∑ b, V b ≤ (T : ℝ) / 2 + 1 / (2 * δ))
    (hR : ∀ b, (T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ)
          + ((T : ℝ) / 2 - 1 / (2 * δ))
          - (ε / δ) * (V b + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V b))
          ≤ R b) :
    ∃ b : Fin m, (1 / 100 : ℝ) * Real.sqrt ((T : ℝ) * m / δ) ≤ R b := by
  sorry
