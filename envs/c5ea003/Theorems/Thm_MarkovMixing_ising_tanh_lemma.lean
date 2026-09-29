-- Prove2me | Theorems.Thm_MarkovMixing_ising_tanh_lemma
-- name    : MarkovMixing.ising_tanh_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:25:43.412576+00:00
-- url     : https://prove2.me/theorems/7b1ec42d-7260-47f1-867d-5aa4f6a934af
-- title:
--   The tanh contraction lemma
-- statement:
--   Fix an inverse temperature $\beta>0$ and consider the function
--   $$g(x)\;=\;\tanh\bigl(\beta(x+1)\bigr)-\tanh\bigl(\beta(x-1)\bigr),$$
--   which measures how much the conditional probability of a $+$ spin under the Ising Glauber dynamics moves when the neighbourhood field increases from $x-1$ to $x+1$ (the heat-bath update at a site with neighbouring spin sum $S$ chooses $+$ with probability $(1+\tanh(\beta S))/2$).
--
--   The theorem (Lemma 15.2 of Levin–Peres–Wilmer) asserts four elementary properties:
--
--   1. $g$ is even: $g(-x)=g(x)$ for every real $x$;
--   2. $g$ is non-increasing on $[0,\infty)$: $0\le x\le y$ implies $g(y)\le g(x)$;
--   3. $g(x)\le 2\tanh\beta$ for every real $x$ — the value at $x=0$ is the global maximum;
--   4. over odd integers the sharper bound holds: $g(k)\le\tanh(2\beta)$ for every odd $k\in\mathbb Z$ — the value at $k=\pm1$ is the maximum among odd integers.
--
--   These four inequalities are the entire analytic content of the high-temperature theorem: in the one-site coupling of two adjacent configurations, the probability that the updated site disagrees is controlled by $g$ evaluated at the neighbouring spin sum, which for a graph with all degrees even is an odd integer — whence the two conditions $\Delta\tanh\beta<1$ and $(\Delta/2)\tanh(2\beta)<1$ of the goal theorem.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.1, Lemma 15.2, Eqs. (15.3)-(15.4), p. 202

import Definitions.Def_mm_ising

namespace MarkovMixing

/-- **Lemma 15.2** (LPW): the function
`ϕ(x) = tanh(β(x+1)) − tanh(β(x−1))` is even, is decreasing on `[0,∞)`,
is bounded by `ϕ(0) = 2 tanh β`, and on odd integers is bounded by
`ϕ(1) = tanh 2β`. -/
theorem ising_tanh_lemma (β : ℝ) (hβ : 0 < β) :
    (∀ x : ℝ, Real.tanh (β * (-x + 1)) - Real.tanh (β * (-x - 1)) =
      Real.tanh (β * (x + 1)) - Real.tanh (β * (x - 1))) ∧
    (∀ x y : ℝ, 0 ≤ x → x ≤ y →
      Real.tanh (β * (y + 1)) - Real.tanh (β * (y - 1)) ≤
        Real.tanh (β * (x + 1)) - Real.tanh (β * (x - 1))) ∧
    (∀ x : ℝ, Real.tanh (β * (x + 1)) - Real.tanh (β * (x - 1)) ≤
      2 * Real.tanh β) ∧
    ∀ k : ℤ, Odd k →
      Real.tanh (β * (k + 1)) - Real.tanh (β * (k - 1)) ≤
        Real.tanh (2 * β) := by
  sorry

end MarkovMixing
