-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_theorem_7_5
-- name    : YeIPA.Asymptotic.theorem_7_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:26.431909+00:00
-- url     : https://prove2.me/theorems/db324b7d-19e0-4890-ac8b-80923780053d
-- title:
--   Theorem 7.5 — the predictor direction satisfies ‖(d_x)_P‖ = O(μ) and ‖(d_s)_Z‖ = O(μ), constant explicit and uniform
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, let $(P,Z)=(P^*,Z^*)$ be the strict complementarity partition of the standard-form pair (LP)–(LD), and let $\mu^0>0$. There is a constant $C>0$, depending only on $(A,b,c)$ and $\mu^0$, such that for every interior point $(x,y,s)$ in the neighbourhood
--   $$\mathcal N_2(1/4)=\{(x,y,s)\in\mathring{\mathcal F}:\ \|Xs-\mu e\|\le\tfrac14\mu\},\qquad\mu=x^Ts/n,$$
--   with $\mu\le\mu^0$, and every solution $(d_x,d_y,d_s)$ of the predictor system (7.4),
--   $$Xd_s+Sd_x=-Xs,\qquad Ad_x=0,\qquad -A^Td_y-d_s=0,$$
--   one has
--   $$\|(d_x)_P\|\le C\mu\qquad\text{and}\qquad\|(d_s)_Z\|\le C\mu .$$
--
--   Together with Lemma 7.3 the whole predictor direction is $O(\mu)$; this is what turns the predictor-corrector algorithm's step into a quadratically convergent one (Theorem 7.6).
--
--   **Formalization Note** The book writes $\|(d_x)_P\|=O(\mu)$ and $\|(d_s)_Z\|=O(\mu)$, with the convention of p. 213 that $O(\cdot)$ "represents a positive quantity that may depend on $n$ and/or the original problem data, but which is independent of the iteration $k$". Here that is the explicit statement $\exists C>0$ before the point: $C$ may depend on $(A,b,c)$ and on $\mu^0$ (the bound $\mu\le\mu^0=(x^0)^Ts^0/n$ that the iterates of Algorithm 4.5 satisfy), never on $(x,y,s)$; a constant chosen after the point would make the statement trivial. The point ranges over $\mathcal N_2(1/4)$, the neighbourhood of the iterates at a predictor step ($\eta=1/4$, p. 213). $\|v_S\|$ is the Euclidean norm of the subvector on $S$. The rank condition on $A$ is the book's standing assumption (stated e.g. on p. 48 and in Theorem 1.15, p. 21).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 216, Theorem 7.5

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP

open Matrix

namespace YeIPA.Asymptotic

/-- Theorem 7.5 (p. 216), with the book's `O(μ)` (p. 213: a positive quantity that may depend
on `n` and the problem data but not on the iterate) made explicit: for LP data with
`rank A = m` and any `μ⁰ > 0` there is `C > 0` such that at every `(x, y, s) ∈ N₂(1/4)` with
`μ = xᵀs/n ≤ μ⁰` the solution of the predictor system (7.4) satisfies
`‖(d_x)_P‖ ≤ Cμ` and `‖(d_s)_Z‖ ≤ Cμ`, `(P, Z) = (P*, Z*)`. -/
theorem theorem_7_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : A.rank = m) (μ0 : ℝ) (hμ0 : 0 < μ0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
        (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ),
        InN2 A b c (1 / 4) x y s → mu x s ≤ μ0 →
        IsPredictorDirection A x s dx dy ds →
          normOn (Pstar A b c) dx ≤ C * mu x s ∧
          normOn (Zstar A b c) ds ≤ C * mu x s := by sorry

end YeIPA.Asymptotic
