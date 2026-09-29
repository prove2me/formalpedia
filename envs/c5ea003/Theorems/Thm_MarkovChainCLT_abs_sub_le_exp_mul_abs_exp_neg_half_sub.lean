-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_sub_le_exp_mul_abs_exp_neg_half_sub
-- name    : MarkovChainCLT.abs_sub_le_exp_mul_abs_exp_neg_half_sub
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:22:11.114021+00:00
-- url     : https://prove2.me/theorems/bc27baf9-74e9-47e3-804f-98685cfd7b43
-- title:
--   Recovering a variance from its Gaussian characteristic value
-- statement:
--   **On a bounded interval, $u \mapsto e^{-u/2}$ has a Lipschitz inverse.** For $a, b \in [0, B]$,
--   $$|a - b| \;\le\; 2 e^{B/2} \, \bigl| e^{-a/2} - e^{-b/2} \bigr| .$$
--
--   **Why the boundedness matters.** The map $u \mapsto e^{-u/2}$ is injective on $[0,\infty)$ but its inverse is not uniformly continuous there: $e^{-a/2}$ and $e^{-b/2}$ can be arbitrarily close while $|a-b|$ is arbitrarily large, provided $a, b$ are both large. Restricting to $[0,B]$ removes this, with the explicit constant $2e^{B/2}$.
--
--   **Where it is used.** The value $e^{-v/2}$ is $\int\cos\,dN(0,v)$. In the truncation argument for the Markov chain central limit theorem, one first shows the numbers $e^{-v_K/2}$ form a Cauchy sequence, by testing the laws against $\cos$; this lemma converts that into the Cauchy property of the variances $v_K$ themselves, using the separately established uniform bound $v_K \le B$.
--
--   **Proof.** By symmetry assume $a \le b$. Then
--   $$e^{-a/2} - e^{-b/2} = e^{-b/2}\bigl( e^{(b-a)/2} - 1 \bigr) \;\ge\; e^{-B/2} \cdot \frac{b-a}{2},$$
--   using $b \le B$ for the first factor and the elementary inequality $e^t \ge 1 + t$ for the second. Multiplying by $2e^{B/2}$ gives $b - a \le 2e^{B/2}(e^{-a/2} - e^{-b/2})$, and both sides of the desired inequality are then read off after removing the absolute values (the right-hand difference is nonnegative in this case).
-- source:
--   Elementary; used in the form needed for G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, and I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971.

import Mathlib.Analysis.SpecialFunctions.Exp

open Filter
open scoped Topology

theorem MarkovChainCLT.abs_sub_le_exp_mul_abs_exp_neg_half_sub (B a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haB : a ≤ B) (hbB : b ≤ B) :
    |a - b| ≤ 2 * Real.exp (B / 2) * |Real.exp (-a / 2) - Real.exp (-b / 2)| := by sorry
