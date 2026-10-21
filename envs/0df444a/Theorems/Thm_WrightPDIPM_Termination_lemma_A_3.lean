-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_lemma_A_3
-- name    : WrightPDIPM.Termination.lemma_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:10.270485+00:00
-- url     : https://prove2.me/theorems/7f681676-80ba-41df-93a8-a1dda22e9e1d
-- title:
--   Lemma A.3 (Hoffman's lemma) — a solution of Gw ≤ g, Hw = h with ‖w‖ ≤ L‖(g, h)‖ for (g, h) ∈ Range([G; H])
-- statement:
--   Let $G \in \mathbb{R}^{r\times q}$ and $H \in \mathbb{R}^{p\times q}$. Then there is a constant $L \ge 0$, depending only on $G$ and $H$, such that for every pair of vectors $(g, h)$ in the range of the stacked matrix $\begin{bmatrix} G \\ H\end{bmatrix}$, the system
--   $$Gw \le g,\qquad Hw = h$$
--   has a solution $w$ with
--   $$\|w\| \le L\,\|(g,h)\|.$$
--
--   This is the form of Hoffman's lemma the book uses to bound the distance from an iterate to the solution set in the analysis of finite termination (Theorem 7.12).
--
--   **Formalization Note** $(g,h) \in \operatorname{Range}([G;H])$ is stated as the existence of $w_0$ with $Gw_0 = g$ and $Hw_0 = h$. $L$ is chosen before $(g, h)$. Norms are Euclidean; $\|(g,h)\| = (\|g\|^2 + \|h\|^2)^{1/2}$. The inequality $Gw \le g$ is componentwise.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 248, Lemma A.3

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Lemma A.3 (Hoffman's lemma, p. 248): for matrices `G ∈ ℝ^{r×q}`, `H ∈ ℝ^{p×q}` there is a
constant `L ≥ 0`, depending only on `G` and `H`, such that for every `(g, h)` in the range of
`[G; H]` the system (A.18) `Gw ≤ g`, `Hw = h` has a solution with `‖w‖ ≤ L‖(g, h)‖`. -/
theorem lemma_A_3 {r p q : ℕ} (G : Matrix (Fin r) (Fin q) ℝ) (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (g : Fin r → ℝ) (h : Fin p → ℝ),
      (∃ w₀ : Fin q → ℝ, G *ᵥ w₀ = g ∧ H *ᵥ w₀ = h) →
        ∃ w : Fin q → ℝ, (∀ i, (G *ᵥ w) i ≤ g i) ∧ H *ᵥ w = h ∧
          norm2 w ≤ L * norm2Pair g h := by sorry

end WrightPDIPM.Termination
