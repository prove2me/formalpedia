-- Prove2me | Theorems.Thm_catalan_ne_rat_mul_sqrt_three_LChiMinusThree
-- name    : catalan_ne_rat_mul_sqrt_three_LChiMinusThree
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T20:16:33.926191+00:00
-- url     : https://prove2.me/theorems/7a432ef7-693a-4a65-9fdf-b76564c56824
-- title:
--   $L(2,\chi_{-4})$ and $\sqrt{3}\,L(2,\chi_{-3})$ are not rationally related
-- statement:
--   Write $G=L(2,\chi_{-4})=\sum_{n\ge0}(-1)^n/(2n+1)^2$ for Catalan's constant and $L(2,\chi_{-3})=\sum_{n\ge0}\big((3n+1)^{-2}-(3n+2)^{-2}\big)$. The assertion is that no rational number $q$ satisfies
--
--   $$G=q\,\sqrt{3}\,L(2,\chi_{-3}),$$
--
--   that is, the ratio
--
--   $$\frac{G}{\sqrt{3}\,L(2,\chi_{-3})}=0.6768661\ldots$$
--
--   is irrational.
--
--   Up to explicit algebraic factors these two numbers are the Dedekind zeta values $\zeta_{\mathbb{Q}(i)}(2)$ and $\zeta_{\mathbb{Q}(\sqrt{-3})}(2)$, and by Humbert's formula they are, up to a rational factor, the covolumes of the two smallest Bianchi groups. The statement is the arithmetic core of Thurston's Question 23: no proof is known, and it is of the same order of difficulty as the irrationality of $\zeta(5)$. It is recorded here as an open target, not as a known theorem.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380): the discussion there reduces the question, for arithmetic examples, to the irrationality of a ratio of Dedekind zeta values at 2. Conjectural statement; no proof is known.

import Mathlib

theorem catalan_ne_rat_mul_sqrt_three_LChiMinusThree (q : ℚ) :
    (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ≠
      (q : ℝ) * (Real.sqrt 3 *
        ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))) := by
  sorry
