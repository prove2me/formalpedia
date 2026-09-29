-- Prove2me | Theorems.Thm_cheb_zeros_props
-- name    : cheb_zeros_props
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T12:25:45.537143+00:00
-- url     : https://prove2.me/theorems/afa2dfb3-7ede-4a3f-aa1f-69bfddaa83cf
-- statement:
--   Properties of the j-th Chebyshev zero t_j := cos((2j+1)pi/(2d)), j = 0..d-1: (1) T_d(t_j) = 0 (since d * (2j+1)pi/(2d) = (2j+1)pi/2 is an odd multiple of pi/2, cos = 0). (2) sign(T'_d(t_j)) = (-1)^j: T'_d(cos theta) = d sin(d theta)/sin theta, sin((2j+1)pi/2) = sin(j pi + pi/2) = cos(j pi) = (-1)^j, and sin((2j+1)pi/(2d)) > 0 (arg in (0,pi)). (3) t_j in (-1,1) since (2j+1)pi/(2d) in (0,pi). Uses T_real_cos, T_derivative_eq_U, U_real_cos.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

theorem cheb_zeros_props (d : ℕ) (hd : 1 ≤ d) (j : ℕ) (hj : j < d) :
    let θj := (2 * (j : ℝ) + 1) * Real.pi / (2 * d);
    (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (Real.cos θj) = 0 ∧
    0 < (-1:ℝ)^j * (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval (Real.cos θj) ∧
    -1 < Real.cos θj ∧ Real.cos θj < 1 := by sorry
