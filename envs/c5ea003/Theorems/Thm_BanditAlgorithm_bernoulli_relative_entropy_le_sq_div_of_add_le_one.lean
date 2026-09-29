-- Prove2me | Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_le_sq_div_of_add_le_one
-- name    : BanditAlgorithm.bernoulli_relative_entropy_le_sq_div_of_add_le_one
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T18:32:43.013124+00:00
-- url     : https://prove2.me/theorems/6d630d2f-5744-457f-957c-ba9d26ab0adb
-- title:
--   Second-order upper bound on the Bernoulli relative entropy: $d(p,q) \le \frac{(q-p)^2}{p\,(2-p-q)}$ when $p < q$ and $p + q \le 1$
-- statement:
--   For reals $0 < p < q$ with $p + q \le 1$,
--   $$d(p,q) \;=\; p\log\frac{p}{q} + (1-p)\log\frac{1-p}{1-q} \;\le\; \frac{(q-p)^2}{p\,(2-p-q)} .$$
--
--   **Why this shape.** The exact second-order behaviour is $d(p,q) = \frac{(q-p)^2}{2\xi(1-\xi)}$ for some $\xi$ between $p$ and $q$, so the sharp denominator as $q \downarrow p$ is $2p(1-p)$; the denominator $p(2-p-q)$ above interpolates to exactly that, so the bound is asymptotically exact. It is strictly sharper than the $\chi^2$ bound $\frac{(q-p)^2}{q(1-q)}$ and than $\frac{(q-p)^2}{2p(1-q)}$, both of which lose the factor $2$ that a Pinsker-type argument needs. The hypothesis $p + q \le 1$ is the natural one: it says the perturbation stays in the region where $x \mapsto x(1-x)$ is at least $p(1-p)$, and it is exactly what fails for the reversed pair.
--
--   **Consequence used downstream.** Since $p + q \le 1$ gives $2 - p - q \ge 1$, one gets the convenient form $d(p, p+\varepsilon) \le \varepsilon^2/p$.
--
--   **Proof.** Bound the two terms separately by the two sharp logarithm estimates, each applied at an argument $\ge 1$: for the first, $\log(p/q) = -\log(q/p) \le -\frac{2(q-p)}{q+p}$ by the Pade lower bound; for the second, $\log\frac{1-p}{1-q} \le \frac12\left(\frac{1-p}{1-q} - \frac{1-q}{1-p}\right)$ by the sinh upper bound. Both estimates are second-order accurate, so their combination is too, and the resulting difference is the exact identity
--   $$\frac{(q-p)^2}{p(2-p-q)} - \left[-\frac{2p(q-p)}{q+p} + \frac{1-p}{2}\left(\frac{1-p}{1-q} - \frac{1-q}{1-p}\right)\right] = \frac{(q-p)^3\,\bigl(2 - 2q - pq - p^2\bigr)}{2p\,(p+q)\,(1-q)\,(2-p-q)},$$
--   whose right-hand side is nonnegative because $p^2 + pq + 2q = p(p+q) + 2q \le p + 2q \le 1 + q \le 2$.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 p. 1584 (the divergence estimate feeding Lemma 13); the inequality itself is the standard second-order bound on the Bernoulli relative entropy, cf. Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Chapter 10.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_bernoulliRelativeEntropy

theorem BanditAlgorithm.bernoulli_relative_entropy_le_sq_div_of_add_le_one
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hsum : p + q ≤ 1) :
    BanditAlgorithm.bernoulliRelativeEntropy p q ≤ (q - p) ^ 2 / (p * (2 - p - q)) := by
  sorry
