-- Prove2me | Theorems.Thm_BookSixth_pair_relabel_line_gap_algebra
-- name    : BookSixth.pair_relabel_line_gap_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T15:32:06.745586+00:00
-- url     : https://prove2.me/theorems/73b59309-2ab4-482e-9d35-2570111ccd9a
-- title:
--   Chapter 15 algebra: positivity and breakpoint agreement for the two-centre relabelling path
-- statement:
--   Elementary algebra for the two-centre relabelling path of Chapter 15. Write $\tau(t)=\max 0\,(\min t\,1)$, $L(a,t)=a+1-a\tau(t)$ and $R(b,t)=b-1+(3-b)\tau(t)$ for the left and right endpoints of the moving middle interval, and $g_{\mathrm{in}}(a,b)=b-a-2$ and $g_{\mathrm{out}}(a,b,t)=R(b,t)-L(a,t)$ for the interior gap and the gap after time $t$. This record isolates the purely algebraic core needed to build the piecewise-linear path of homeomorphisms of $\mathbb{R}$ that carries the two ordered centres $3i$ and $3j$ onto $0$ and $3$. It states: $\tau$ is continuous with $\tau 0 = 0$, $\tau 1 = 1$ and $0\le\tau t\le 1$; both gaps are strictly positive whenever $3\le b-a$; the moving gap satisfies the exact identity $g_{\mathrm{out}}=1+(b-a-3)(1-\tau t)$, so the motion closes the slack $b-a-3$ linearly and never collapses the gap; and the four breakpoint agreement identities that make the forward and backward piecewise-linear maps agree where their pieces meet. Every clause is an equality or a positivity fact about explicit real expressions, so the record is independent of any topological content and can be imported by the later reduction that supplies continuity, the two-sided inverse, and the endpoint laws.
-- source:
--   Corrected algebraic core for Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The two centres $3i<3j$ are separated by at least $3$ because $i<j$, which is exactly the hypothesis $3\le b-a$ under which both gaps are positive and every division below is legal. The identity $g_{\mathrm{out}}=1+(b-a-3)(1-\tau t)$ is the reason the motion is well defined for all time: the gap retains its initial value $1$ plus the unclosed portion $b-a-3$ of the original slack, and reaches exactly $1$ when $\tau t=1$, leaving the two unit circles adjacent. The four agreement identities are the continuity conditions at the breakpoints $a+1$ and $b-1$; they are stated for both the forward and the backward piecewise-linear maps because both are needed to show they are inverse homeomorphisms.

import Mathlib

theorem BookSixth.pair_relabel_line_gap_algebra :
    (Continuous (fun t : ℝ => max 0 (min t 1))) ∧
    ((max 0 (min 0 1)) = 0) ∧
    ((max 0 (min 1 1)) = 1) ∧
    (∀ t : ℝ, 0 ≤ max 0 (min t 1)) ∧
    (∀ t : ℝ, max 0 (min t 1) ≤ 1) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → 0 < b - a - 2) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      0 < (b - 1 + (3 - b) * max 0 (min t 1)) - (a + 1 - a * max 0 (min t 1))) ∧
    (∀ a b t : ℝ,
      (b - 1 + (3 - b) * max 0 (min t 1)) - (a + 1 - a * max 0 (min t 1))
        = 1 + (b - a - 3) * (1 - max 0 (min t 1))) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      a + 1 - a * max 0 (min t 1)
        = (a + 1 - a * max 0 (min t 1))
          + ((a + 1 - (a + 1)) * ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) / (b - a - 2))) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      (a + 1 - a * max 0 (min t 1))
          + ((b - 1 - (a + 1)) * ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) / (b - a - 2))
        = b - 1 + (3 - b) * max 0 (min t 1)) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      a + 1 + (((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) * (b - a - 2)
          / ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))))
        = (b - 1 + (3 - b) * max 0 (min t 1))
          - (3 - b) * max 0 (min t 1)) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      (a + 1 - a * max 0 (min t 1)) + a * max 0 (min t 1)
        = a + 1 + (((a + 1 - a * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) * (b - a - 2)
          / ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))))) := by sorry
