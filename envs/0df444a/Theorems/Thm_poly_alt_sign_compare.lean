-- Prove2me | Theorems.Thm_poly_alt_sign_compare
-- name    : poly_alt_sign_compare
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T12:25:50.225857+00:00
-- url     : https://prove2.me/theorems/264abaee-a940-4f99-9870-b5b963be8352
-- statement:
--   Root-counting comparison lemma (the algebraic core of Chebyshev comparison arguments). Given polynomials Tp, p of degree <= n, and n+1 strictly decreasing points t_0 > t_1 > ... > t_n such that Tp alternates strictly in sign at the t_i (sign(Tp(t_i)) = (-1)^i) and |p(t_i)| <= |Tp(t_i)|: then |p(c)| <= |Tp(c)| for all c outside the open interval (t_n, t_0). Proof: Step 1 (sign preservation for Tp): Tp has n sign changes at the t_i, hence n distinct roots r_i in (t_{i+1}, t_i) by IVT. Since deg Tp <= n, these are all the roots. So Tp has no roots in [t_0, infinity) or (-infinity, t_n]. Since Tp(t_0) > 0, Tp(c) > 0 for c >= t_0 (else IVT gives a root >= t_0). Similarly (-1)^n Tp(c) > 0 for c <= t_n. Step 2 (comparison): suppose |p(c)| > |Tp(c)| for some c >= t_0. WLOG p(c) > Tp(c) > 0 (negate p if needed). Let mu := Tp(c)/p(c) in (0,1). R := Tp - mu * p. R(c) = 0. At t_i: (-1)^i R(t_i) = (-1)^i Tp(t_i) - mu (-1)^i p(t_i) >= |Tp(t_i)| - mu |p(t_i)| >= (1-mu)|Tp(t_i)| > 0. So R alternates strictly at t_i, n sign changes, n distinct roots in (t_n, t_0). Plus R(c) = 0 with c >= t_0 > all those roots. n+1 distinct roots. deg R <= n. R != 0 (R(t_0) > 0). Contradiction with card_roots' <= natDegree <= n. Symmetric for c <= t_n. Uses Polynomial.card_roots', IVT (intermediate_value_Ioo or intermediate_value_Icc), Polynomial.continuous / Polynomial.continuousOn. NOT in Mathlib.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

theorem poly_alt_sign_compare (Tp p : Polynomial ℝ) (n : ℕ) (t : ℕ → ℝ)
    (ht : ∀ i j : ℕ, i < j → j ≤ n → t j < t i)
    (hTdeg : Tp.natDegree ≤ n) (hpdeg : p.natDegree ≤ n)
    (halt : ∀ i : ℕ, i ≤ n → 0 < (-1:ℝ)^i * Tp.eval (t i))
    (hcmp : ∀ i : ℕ, i ≤ n → |p.eval (t i)| ≤ |Tp.eval (t i)|) :
    ∀ c : ℝ, (t 0 ≤ c ∨ c ≤ t n) → |p.eval c| ≤ |Tp.eval c| := by sorry
