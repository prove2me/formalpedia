-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_exact_shell_parameters
-- name    : ZLIPPadding.Padding.Supplement.exact_shell_parameters
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:21:06.405614+00:00
-- url     : https://prove2.me/theorems/2f310df0-2798-4e0f-bca3-fc8074c72998
-- title:
--   Proposition 4.3 — Exact signed shell counting and resource bounds
-- statement:
--   There are absolute positive constants, independent of $n,m$, for the following algorithm. Given integers $n\ge2$ and $m\ge1$, the explicit dynamic program decides whether $S_m(\mathbb Z^n)$ is empty. In the nonempty case it returns the exact rational values
--
--   $$\alpha=\frac{Q_4}{R},\qquad\beta=\frac{Q_{22}}{R},\qquad\kappa=\frac{Q_4-3Q_{22}}{R},$$
--
--   and thus determines the positive, negative, or zero sign of $\kappa$. Here $R=R_n(m)$, $Q_4$ and $Q_{22}$ are the counts in (4.10)–(4.11). The actual executed integer arithmetic uses $O(nm^{3/2})$ operations, with all logged intermediate integers and output rational numerators and denominators using $O(n\log(m+1))$ bits. Correctness and both bounds are conclusions, not assumptions about a supplied counting oracle. This is the sign preprocessing for Theorem 4.1.
--
--   Differences from the source:
--   - encoding: O(nm^(3/2)) integer operations on O(n log(m+1))-bit integers → absolute constants before n,m, an executed arithmetic log and base-two bit lengths; reason: the operation and bit models express the same bounds up to absolute constants
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 17 (PDF p. 18), Proposition 4.3

import Definitions.Def_ZLIPPadding_Padding_Supplement_Counting

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem exact_shell_parameters :
    ∃ C1 C2 : ℕ, 0 < C1 ∧ 0 < C2 ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m →
      (countResult n m = none ↔ shell n m = ∅) ∧
      countResult n m = countedParameters n m ∧
      (∀ alpha beta kap : ℚ, countResult n m = some (alpha,beta,kap) →
        (alpha : ℝ) = shellAlpha n m ∧ (beta : ℝ) = shellBeta n m ∧
        (kap : ℝ) = shellKappa n m ∧
        ∀ q ∈ [alpha,beta,kap], integerBits q.num + q.den.bits.length ≤
          C2*n*(Nat.log2 (m+1)+1)) ∧
      ((countLog n m).operations : ℝ) ≤ (C1 : ℝ)*n*m*Real.sqrt m ∧
      (∀ v ∈ (countLog n m).values,
        integerBits v ≤ C2*n*(Nat.log2 (m+1)+1)) := by sorry

end ZLIPPadding.Padding.Supplement
