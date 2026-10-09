-- Prove2me | Theorems.Thm_YuanDGD_Linear_lemma_2
-- name    : YuanDGD.Linear.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:29.349927+00:00
-- url     : https://prove2.me/theorems/aa8bf2b0-5987-4d40-b76b-5f6ed35f6b62
-- title:
--   Lemma 2, p. 10 — ‖∇fᵢ(x₍ᵢ₎(k)) − ∇fᵢ(x̄(k))‖ ≤ αDL_fᵢ/(1 − β) and ‖g(k) − ḡ(k)‖ ≤ αDL_h/(1 − β)
-- statement:
--   Let $W$ be a symmetric doubly stochastic $n\times n$ matrix, $n\ge2$, with $\beta<1$, and let each $f_i:\mathbb R^p\to\mathbb R$ have an $L_{f_i}$-Lipschitz gradient, $L_{f_i}>0$; put $L_h=\max_iL_{f_i}$. Run DGD (4) from $0$ with stepsize $\alpha>0$, and write $\bar x(k)$ for the mean, $g(k)=\frac1n\sum_i\nabla f_i(x_{(i)}(k))$ and $\bar g(k)=\frac1n\sum_i\nabla f_i(\bar x(k))$. If the stacked gradients satisfy $\|h(s)\|\le B$ for every $s\ge0$, then for every $k\ge0$ and every agent $i$,
--   $$
--   \|\nabla f_i(x_{(i)}(k))-\nabla f_i(\bar x(k))\|\le\frac{\alpha BL_{f_i}}{1-\beta},\qquad \|g(k)-\bar g(k)\|\le\frac{\alpha BL_h}{1-\beta}.
--   $$
--
--   With $B=D$ this is the paper's Lemma 2. It measures how far the averaged update direction $g(k)$ is from the exact gradient $\bar g(k)=\nabla\bar f(\bar x(k))$ of $\bar f=\frac1n\sum_if_i$, which is the error term of Theorem 3.
--
--   **Formalization Note** As in Lemma 1, "(10) holds" is stated for a generic bound $B$ (the page's $D$ is the instance $B=D$). Of Assumption 1 only the Lipschitz gradients with $L_{f_i}>0$, the conditions on $W$, $\beta<1$ and $n\ge2$ are kept; convexity, differentiability and lower boundedness are not used.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 10, Lemma 2

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace
open Matrix

namespace YuanDGD.Linear

/-- Lemma 2, p. 10: with `L_fᵢ`-Lipschitz gradients, bounded stacked gradients (bound `B`,
as (10) gives with `B = D`) and `β < 1`, the local gradients at `x₍ᵢ₎(k)` and at `x̄(k)` differ
by at most `αBL_fᵢ/(1 − β)`, and `‖g(k) − ḡ(k)‖ ≤ αBL_h/(1 − β)`. -/
theorem lemma_2 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ)
    (Lf : Fin n → ℝ) (hn : 2 ≤ n) (hsymm : Wᵀ = W) (hds : W ∈ doublyStochastic ℝ (Fin n))
    (hβ : beta W < 1) (hLf : ∀ i, 0 < Lf i)
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ Lf i * ‖a - b‖)
    (α : ℝ) (hα : 0 < α) (B : ℝ) (hB : ∀ s : ℕ, ‖hvec f (dgd W f α) s‖ ≤ B) :
    (∀ (k : ℕ) (i : Fin n),
        ‖gradient (f i) (dgd W f α k i) - gradient (f i) (xbar (dgd W f α) k)‖ ≤
          α * B * Lf i / (1 - beta W)) ∧
      ∀ k : ℕ, ‖gk f (dgd W f α) k - gbar f (dgd W f α) k‖ ≤ α * B * Lh Lf / (1 - beta W) := by sorry

end YuanDGD.Linear
