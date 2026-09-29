-- Prove2me | Theorems.Thm_jacobian_conjecture
-- name    : jacobian_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T18:49:56.023118+00:00
-- url     : https://prove2.me/theorems/41df4359-5a25-4def-8d1f-3926938bb196
-- statement:
--   **Jacobian Conjecture**: If $F = (F_1, \ldots, F_n) : \mathbb{C}^n \to \mathbb{C}^n$ is a polynomial map whose Jacobian determinant $\det(\partial F_i/\partial x_j)$ is a non-zero constant, then $F$ is bijective (and has a polynomial inverse).
--
--   Proposed by Keller (1939). Open for $n \geq 2$. Equivalent to many other open problems in algebra. Known to hold for maps of degree $\leq 2$ in all dimensions. A deep result (Yagzhev, Bass-Connell-Wright) reduces it to maps of the form $x \mapsto x + H(x)$ where $H$ is cubic homogeneous.
--
--   **Source**: Bass, H., Connell, E.H., Wright, D. (1982). Bulletin of the AMS, 7(2), 287–330. DOI:10.1090/S0273-0979-1982-15032-7
-- source:
--   https://en.wikipedia.org/wiki/Jacobian_conjecture

import Mathlib

theorem jacobian_conjecture (n : ℕ) (hn : 0 < n)
    (F : Fin n → MvPolynomial (Fin n) ℂ)
    (hJ : ∃ c : ℂ, c ≠ 0 ∧
      Matrix.det (Matrix.of (fun i j => MvPolynomial.pderiv j (F i))) =
      MvPolynomial.C c) :
    Function.Bijective (fun x : Fin n → ℂ =>
      fun i => MvPolynomial.eval x (F i)) := by
  sorry
