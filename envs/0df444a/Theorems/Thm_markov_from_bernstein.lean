-- Prove2me | Theorems.Thm_markov_from_bernstein
-- name    : markov_from_bernstein
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T07:55:54.652576+00:00
-- url     : https://prove2.me/theorems/78dded16-5422-412f-8191-39b72dc08a9e
-- statement:
--   The 'Markov-from-Bernstein' step (Exercise 7.7 of Cambridge Part III approximation theory notes; the last step of A. Markov's 1889 proof). If p has degree < d and satisfies the Bernstein-type pointwise bound (1-x^2) p(x)^2 <= d^2 on [-1,1] (equivalently |p(x)| <= d/sqrt(1-x^2)), then |p| <= d^2 uniformly on [-1,1]. Proof: (a) For |x| <= cos(pi/(2d)): 1-x^2 >= sin^2(pi/(2d)) >= 1/d^2, so d/sqrt(1-x^2) <= d^2. (b) For |x| >= cos(pi/(2d)) (outside the zeros of T_d): |p(t_j)| <= d/sqrt(1-t_j^2) = |T'_d(t_j)| at the d zeros t_j of T_d, with T'_d alternating sign there; a root-counting argument (for lambda in (0,1), T'_d - lambda p has d-1 sign alternations hence exactly d-1 simple roots in (t_d, t_1), degree d-1, so it has a constant sign outside that interval) gives |p(x)| <= |T'_d(x)| for |x| >= cos(pi/(2d)), and |T'_d| <= d^2 on [-1,1]. NOT in Mathlib.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem markov_from_bernstein (p : Polynomial ℝ) {d : ℕ} (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → |p.eval c| ≤ (d : ℝ)^2 := by sorry
