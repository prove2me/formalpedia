-- Prove2me | Theorems.Thm_YuanDGD_Linear_lemma_1
-- name    : YuanDGD.Linear.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:31.809981+00:00
-- url     : https://prove2.me/theorems/62a71740-b006-4717-8d09-9c83dc116db6
-- title:
--   Lemma 1, p. 8 — the deviation from the mean is at most αD/(1 − β)
-- statement:
--   Let $W$ be a symmetric doubly stochastic $n\times n$ matrix, $n\ge2$, with $\beta=\max\{|\lambda_2(W)|,|\lambda_n(W)|\}<1$. Let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be arbitrary, $\alpha>0$, and let $x_{(i)}(k)$ be the DGD iterates (4) started from $x_{(i)}(0)=0$, with stacked gradients $h(k)$ and mean $\bar x(k)=\frac1n\sum_ix_{(i)}(k)$. If $\|h(s)\|\le B$ for every $s\ge0$, then for every $k\ge0$ and every agent $i$,
--   $$
--   \|x_{(i)}(k)-\bar x(k)\|\le\frac{\alpha B}{1-\beta}.
--   $$
--
--   With $B=D$ from (10) (Theorem 1) this is the paper's Lemma 1, $\|x_{(i)}(k)-\bar x(k)\|\le\alpha D/(1-\beta)$: the agents stay in an $O(\alpha/(1-\beta))$ neighbourhood of their mean. Corollary 1 combines it with the rate of the mean.
--
--   **Formalization Note** The page's hypothesis "(10) holds" is stated for a generic bound $B$ on $\|h(s)\|$; the page's $D$ is the instance $B=D$, so the item is at least as strong as the page's lemma. Only the parts of Assumption 1 the lemma uses are kept (symmetry and double stochasticity of $W$, $\beta<1$, $n\ge2$); no property of the $f_i$ is needed. The start $x_{(i)}(0)=0$ is built into the iteration.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 8, Lemma 1

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace
open Matrix

namespace YuanDGD.Linear

/-- Lemma 1, p. 8: if the stacked gradients of DGD are bounded by `B` (as (10) gives with
`B = D`) and `β < 1`, every agent stays within `αB/(1 − β)` of the mean. -/
theorem lemma_1 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ)
    (hn : 2 ≤ n) (hsymm : Wᵀ = W) (hds : W ∈ doublyStochastic ℝ (Fin n))
    (hβ : beta W < 1) (α : ℝ) (hα : 0 < α) (B : ℝ)
    (hB : ∀ s : ℕ, ‖hvec f (dgd W f α) s‖ ≤ B) :
    ∀ (k : ℕ) (i : Fin n), ‖dgd W f α k i - xbar (dgd W f α) k‖ ≤ α * B / (1 - beta W) := by sorry

end YuanDGD.Linear
