-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_theorem_1_bound
-- name    : YuanDGD.Sublinear.theorem_1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:27.705571+00:00
-- url     : https://prove2.me/theorems/8b94e25a-ac63-404f-ad96-132528f15cf1
-- title:
--   Theorem 1, (10), p. 7 — for α ≤ (1 + λₙ(W))/L_h the stacked gradient obeys ‖h(k)‖ ≤ D for every k
-- statement:
--   Under Assumption 1, let the stepsize satisfy
--   $$0 < \alpha \le \frac{1 + \lambda_n(W)}{L_h}. \qquad (9)$$
--   Then the DGD iterates (4), started from $x_{(i)}(0) = 0$, satisfy for every $k \ge 0$
--   $$\|h(k)\| = \Big(\sum_{i=1}^n \|\nabla f_i(x_{(i)}(k))\|^2\Big)^{1/2} \le D = \sqrt{2L_h\sum_{i=1}^n\big(f_i(0) - f_i^o\big)}.$$
--
--   The local gradients stay bounded without any bounded-gradient assumption; the bound depends only on the data at the starting point. Lemmas 1 and 2 and Theorem 2 use it.
--
--   **Formalization Note.** Only the bound (10) of Theorem 1 is posed; its first sentence (convergence of the iterates) is not, since it fails at the boundary $\alpha = (1+\lambda_n(W))/L_h$. The paper states (10) for $k = 1, 2, \dots$; it is stated here for every $k \ge 0$, which is what Lemma 1's proof uses and holds by the same argument. $f_i^o$ is $\inf f_i$. $\alpha > 0$ is the reading of "stepsize".
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 7, Theorem 1, (9)–(10)

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, Theorem 1, (10), p. 7: under Assumption 1, if
`0 < α ≤ (1 + λₙ(W))/L_h` (9), then the DGD iterates (4) started from `x₍ᵢ₎(0) = 0` satisfy
`‖h(k)‖ ≤ D = √(2L_h Σᵢ (fᵢ(0) − fᵢᵒ))` for every `k ≥ 0`. -/
theorem theorem_1_bound {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf) :
    ∀ k : ℕ, ‖hvec f (dgd W f α) k‖ ≤ D f Lf := by sorry

end YuanDGD.Sublinear
