-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_lemma_7_3
-- name    : YeIPA.Asymptotic.lemma_7_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:27.484986+00:00
-- url     : https://prove2.me/theorems/d5576664-2382-4ce1-9f24-fad47d649e4e
-- title:
--   Lemma 7.3 — the predictor direction satisfies ‖(d_x)_Z‖ = O(μ) and ‖(d_s)_P‖ = O(μ), constant explicit and uniform
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, let $(P,Z)=(P^*,Z^*)$ be the strict complementarity partition, and let $\mu^0>0$. There is a constant $C>0$, depending only on $(A,b,c)$ and $\mu^0$, such that for every $(x,y,s)\in\mathcal N_2(1/4)$ with $\mu=x^Ts/n\le\mu^0$ and every solution $(d_x,d_y,d_s)$ of the predictor system (7.4),
--   $$Xd_s+Sd_x=-Xs,\qquad Ad_x=0,\qquad -A^Td_y-d_s=0,$$
--   one has
--   $$\|(d_x)_Z\|\le C\mu\qquad\text{and}\qquad\|(d_s)_P\|\le C\mu .$$
--
--   These are the "easy" halves of the $O(\mu)$ estimate of the predictor direction: on the indices where the variable tends to zero, the step is of the order of the duality gap.
--
--   **Formalization Note** The book writes $\|(d_x)_Z\|=O(\mu)$ and $\|(d_s)_P\|=O(\mu)$, with the convention of p. 213 that $O(\cdot)$ "represents a positive quantity that may depend on $n$ and/or the original problem data, but which is independent of the iteration $k$". Here that is the explicit statement $\exists C>0$ before the point: $C$ may depend on $(A,b,c)$ and on $\mu^0$ (the bound on $\mu$ that the iterates of Algorithm 4.5 satisfy with $\mu^0=(x^0)^Ts^0/n$), never on $(x,y,s)$. The point ranges over $\mathcal N_2(1/4)$, the neighbourhood the iterates lie in at a predictor step (p. 214). $\|v_S\|$ is the Euclidean norm of the subvector on $S$. The rank condition on $A$ is the book's standing assumption.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 214, Lemma 7.3

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP

open Matrix

namespace YeIPA.Asymptotic

/-- Lemma 7.3 (p. 214), with the book's `O(μ)` (p. 213: a positive quantity that may depend
on `n` and the problem data but not on the iterate) made explicit: for LP data with
`rank A = m` and any `μ⁰ > 0` there is `C > 0` such that at every `(x, y, s) ∈ N₂(1/4)` with
`μ = xᵀs/n ≤ μ⁰` the solution of the predictor system (7.4) satisfies
`‖(d_x)_Z‖ ≤ Cμ` and `‖(d_s)_P‖ ≤ Cμ`, `(P, Z) = (P*, Z*)`. -/
theorem lemma_7_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : A.rank = m) (μ0 : ℝ) (hμ0 : 0 < μ0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
        (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ),
        InN2 A b c (1 / 4) x y s → mu x s ≤ μ0 →
        IsPredictorDirection A x s dx dy ds →
          normOn (Zstar A b c) dx ≤ C * mu x s ∧
          normOn (Pstar A b c) ds ≤ C * mu x s := by sorry

end YeIPA.Asymptotic
