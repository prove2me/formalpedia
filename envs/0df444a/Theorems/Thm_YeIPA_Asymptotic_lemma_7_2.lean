-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_lemma_7_2
-- name    : YeIPA.Asymptotic.lemma_7_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:20.746413+00:00
-- url     : https://prove2.me/theorems/c76be1f0-56cf-4db6-8be2-4549d471acb9
-- title:
--   Lemma 7.2 — if Xd_s + Sd_x = −Xs and d_xᵀd_s ≥ 0, then ‖D⁻¹d_x‖² + ‖Dd_s‖² ≤ xᵀs
-- statement:
--   Let $x,s\in\mathbb R^n$ with $x>0$, $s>0$, let $X=\operatorname{diag}(x)$, $S=\operatorname{diag}(s)$, and let $D=X^{1/2}S^{-1/2}$, the diagonal matrix with entries $D_j=\sqrt{x_j/s_j}$. If $d_x,d_s\in\mathbb R^n$ satisfy the equation
--   $$Xd_s+Sd_x=-Xs$$
--   and the inequality $(d_x)^Td_s\ge0$, then
--   $$\|D^{-1}d_x\|^2+\|Dd_s\|^2\le x^Ts .$$
--
--   The lemma bounds the scaled predictor direction by the duality gap; Chapter 7 applies it to the LP system (7.4), where $(d_x)^Td_s=0$, and to monotone LCPs, where $(d_x)^Td_s\ge0$.
--
--   **Formalization Note** The positivity $x>0$, $s>0$ is implicit on p. 214 (it is needed for $D$ to exist) and is a hypothesis here. $\|D^{-1}d_x\|^2$ is written $\sum_j (d_{x,j}/D_j)^2$ and $\|Dd_s\|^2$ as $\sum_j (D_j d_{s,j})^2$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 214, Lemma 7.2

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP

open Matrix

namespace YeIPA.Asymptotic

/-- Lemma 7.2 (p. 214). Let `x, s > 0` and `D = X^{1/2} S^{-1/2}`, `Dⱼ = √(xⱼ/sⱼ)`. If
`d_x, d_s` satisfy `X d_s + S d_x = −Xs` and `(d_x)ᵀ d_s ≥ 0`, then
`‖D⁻¹ d_x‖² + ‖D d_s‖² ≤ xᵀs`. -/
theorem lemma_7_2 {n : ℕ} (x s dx ds : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (heq : ∀ j, x j * ds j + s j * dx j = -(x j * s j))
    (hmono : 0 ≤ dx ⬝ᵥ ds) :
    ∑ j, (dx j / scaling x s j) ^ 2 + ∑ j, (scaling x s j * ds j) ^ 2 ≤ x ⬝ᵥ s := by sorry

end YeIPA.Asymptotic
