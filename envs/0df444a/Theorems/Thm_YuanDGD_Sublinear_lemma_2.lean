-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_lemma_2
-- name    : YuanDGD.Sublinear.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:30.209892+00:00
-- url     : https://prove2.me/theorems/8ab000e3-31e9-4552-81aa-88f2778d3db9
-- title:
--   Lemma 2, p. 10 — ‖∇fᵢ(x₍ᵢ₎(k)) − ∇fᵢ(x̄(k))‖ ≤ αBL_fᵢ/(1 − β) and ‖g(k) − ḡ(k)‖ ≤ αBL_h/(1 − β)
-- statement:
--   Let $n \ge 2$, let $W$ be symmetric and doubly stochastic with $\beta < 1$, and let $\alpha > 0$. Suppose each $\nabla f_i$ is Lipschitz with constant $L_{f_i} > 0$. Run DGD (4) from $0$ and suppose $\|h(s)\| \le B$ for every $s \ge 0$. Then for all $k \ge 0$ and all $i$,
--   $$\|\nabla f_i(x_{(i)}(k)) - \nabla f_i(\bar x(k))\| \le \frac{\alpha B L_{f_i}}{1-\beta}, \qquad \|g(k) - \bar g(k)\| \le \frac{\alpha B L_h}{1-\beta},$$
--   where $g(k) = \frac1n\sum_i \nabla f_i(x_{(i)}(k))$, $\bar g(k) = \frac1n\sum_i \nabla f_i(\bar x(k))$ and $L_h = \max_i L_{f_i}$.
--
--   The second inequality says that the averaged DGD step is an inexact gradient step for $\bar f$, with an error of order $\alpha/(1-\beta)$; Theorem 2 uses it with $B = D$.
--
--   **Formalization Note.** As in Lemma 1, the hypothesis "(10) holds" is taken with a generic bound $B$; the paper's statement is $B = D$. Of Assumption 1 only the Lipschitz gradients (with $L_{f_i} > 0$) and the conditions on $W$ are used.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 10, Lemma 2

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

open Matrix

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, Lemma 2, p. 10, with a generic bound `B` in place of `D`:
under the hypotheses of Lemma 1 and Lipschitz gradients `‖∇fᵢ(a) − ∇fᵢ(b)‖ ≤ L_fᵢ‖a − b‖` with
`L_fᵢ > 0`, `‖∇fᵢ(x₍ᵢ₎(k)) − ∇fᵢ(x̄(k))‖ ≤ αBL_fᵢ/(1 − β)` and `‖g(k) − ḡ(k)‖ ≤ αBL_h/(1 − β)`. -/
theorem lemma_2 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ)
    (hn : 2 ≤ n) (hsymm : Wᵀ = W) (hds : W ∈ doublyStochastic ℝ (Fin n)) (hβ : beta W < 1)
    (hLf : ∀ i, 0 < Lf i)
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ Lf i * ‖a - b‖)
    (α : ℝ) (hα : 0 < α) (B : ℝ) (hB : ∀ s : ℕ, ‖hvec f (dgd W f α) s‖ ≤ B) :
    (∀ (k : ℕ) (i : Fin n),
      ‖gradient (f i) (dgd W f α k i) - gradient (f i) (xbar (dgd W f α) k)‖
        ≤ α * B * Lf i / (1 - beta W)) ∧
    ∀ k : ℕ, ‖gk f (dgd W f α) k - gbar f (dgd W f α) k‖ ≤ α * B * Lh Lf / (1 - beta W) := by sorry

end YuanDGD.Sublinear
