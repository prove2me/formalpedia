-- Prove2me | Theorems.Thm_LinearOptimization_fourier_motzkin_projection
-- name    : LinearOptimization.fourier_motzkin_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T01:18:27.84267+00:00
-- url     : https://prove2.me/theorems/2a04c272-08d8-4973-a218-8eab7c138b8e
-- title:
--   Fourier–Motzkin elimination computes the projection
-- statement:
--   **(Theorem 2.10, GOAL)** The polyhedron $Q$ constructed by the elimination algorithm is equal to the projection $\Pi_{n-1}(P)$ of $P$, where for $S \subset \mathbb{R}^n$,
--
--   $$\Pi_k(S) = \{\pi_k(x) \mid x \in S\} \quad \text{and} \quad \pi_k(x_1, \dots, x_n) = (x_1, \dots, x_k).$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.10, p. 73

import Definitions.Def_FourierMotzkinStep


/-- **Bertsimas & Tsitsiklis, Theorem 2.10 (p. 73).** One Fourier–Motzkin elimination step
computes exactly the projection of the polyhedron onto its first `n`
coordinates. -/

theorem LinearOptimization.fourier_motzkin_projection {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) :
    fourierMotzkinEliminate A b =
      (fun x : Fin (n + 1) → ℝ => fun l : Fin n => x l.castSucc) ''
        polyhedron A b := by
  sorry
