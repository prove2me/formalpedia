-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_lemma_1
-- name    : YuanDGD.Sublinear.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:21.480625+00:00
-- url     : https://prove2.me/theorems/21982668-b000-4524-b907-efc38414390a
-- title:
--   Lemma 1, p. 8 — if ‖h(s)‖ ≤ B for all s and β < 1, every agent stays within αB/(1 − β) of the mean
-- statement:
--   Let $n \ge 2$, let $W$ be symmetric and doubly stochastic with $\beta < 1$, let $\alpha > 0$, and let $f_1,\dots,f_n : \mathbb R^p \to \mathbb R$ be arbitrary. Run DGD (4) from $x_{(i)}(0) = 0$. If $B$ is a real number with $\|h(s)\| \le B$ for every $s \ge 0$, then
--   $$\|x_{(i)}(k) - \bar x(k)\| \le \frac{\alpha B}{1-\beta} \qquad \text{for all } k \ge 0 \text{ and all } i.$$
--
--   This is the bounded deviation from the mean: the agents stay in approximate consensus. With $B = D$ from (10) it is Lemma 1 of the paper.
--
--   **Formalization Note.** The paper's hypothesis "(10) holds" is stated with a generic bound $B$ in place of $D$; the paper's statement is the instance $B = D$. No convexity or smoothness of the $f_i$ is used, so those hypotheses are dropped; the start $x_{(i)}(0) = 0$ is built into the iteration.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 8, Lemma 1

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

open Matrix

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, Lemma 1, p. 8, with a generic bound `B` in place of `D`: if
`W` is symmetric and doubly stochastic with `β < 1`, `n ≥ 2`, `α > 0`, and `‖h(s)‖ ≤ B` for every
`s`, then the DGD iterates (4) from `0` satisfy `‖x₍ᵢ₎(k) − x̄(k)‖ ≤ αB/(1 − β)` for all `k`, `i`. -/
theorem lemma_1 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ)
    (hn : 2 ≤ n) (hsymm : Wᵀ = W) (hds : W ∈ doublyStochastic ℝ (Fin n)) (hβ : beta W < 1)
    (α : ℝ) (hα : 0 < α) (B : ℝ) (hB : ∀ s : ℕ, ‖hvec f (dgd W f α) s‖ ≤ B) :
    ∀ (k : ℕ) (i : Fin n), ‖dgd W f α k i - xbar (dgd W f α) k‖ ≤ α * B / (1 - beta W) := by sorry

end YuanDGD.Sublinear
