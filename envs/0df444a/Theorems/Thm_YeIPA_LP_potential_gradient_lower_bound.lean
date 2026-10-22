-- Prove2me | Theorems.Thm_YeIPA_LP_potential_gradient_lower_bound
-- name    : YeIPA.LP.potential_gradient_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:28.411761+00:00
-- url     : https://prove2.me/theorems/abd478e5-0446-4f3a-9e14-80c3dc17caeb
-- title:
--   Lemma 4.12 — $\sqrt{\min(v)}\,\|V^{-1/2}(e-\frac{n+\rho}{e^Tv}v)\|\ge\sqrt{3/4}$ for $\rho\ge\sqrt n$
-- statement:
--   Let $n\ge1$, let $v\in\mathbb R^n$ be a positive vector, $V=\operatorname{diag}(v)$, $\min(v)=\min_jv_j$, and let $\rho\ge\sqrt n$. Then
--   $$\sqrt{\min(v)}\,\Big\|V^{-1/2}\Big(e-\frac{n+\rho}{e^Tv}\,v\Big)\Big\|\ \ge\ \sqrt{3/4},$$
--   where $\|\cdot\|$ is the Euclidean norm.
--
--   Applied to $v=Xs$, this bounds from below the first-order decrease in Lemma 4.11, so that the symmetric primal-dual step lowers the potential by at least $\alpha\sqrt{3/4}-\alpha^2/(2(1-\alpha))$.
--
--   **Formalization Note** The book leaves the proof as Exercise 4.8; the hypotheses are those printed. $V^{-1/2}w$ is written componentwise as $w_j/\sqrt{v_j}$. The condition $n\ge1$ is implicit in "a positive vector" and is a hypothesis (for $n=0$ the left side is not meaningful).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 127, Lemma 4.12

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix

namespace YeIPA.LP

/-- Lemma 4.12 (Ye 1997, p. 127; proof is Exercise 4.8). Let `v ∈ ℝⁿ` be a positive vector
(`n ≥ 1`) and `ρ ≥ √n`. Then `√min(v) ‖V^{-1/2}(e − ((n + ρ)/(eᵀv)) v)‖ ≥ √(3/4)`. -/
theorem potential_gradient_lower_bound {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ)
    (hv : ∀ j, 0 < v j) (ρ : ℝ) (hρ : Real.sqrt n ≤ ρ) :
    Real.sqrt (3 / 4) ≤
      Real.sqrt (vmin v) *
        norm2 (fun j => (1 - ((n : ℝ) + ρ) / (∑ i, v i) * v j) / Real.sqrt (v j)) := by sorry

end YeIPA.LP
