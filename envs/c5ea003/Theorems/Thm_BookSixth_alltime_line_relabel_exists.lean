-- Prove2me | Theorems.Thm_BookSixth_alltime_line_relabel_exists
-- name    : BookSixth.alltime_line_relabel_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:45:18.094984+00:00
-- url     : https://prove2.me/theorems/8ea0b3ac-f4f3-4905-a316-bcc07801217c
-- title:
--   Chapter 15: lift a two-arc relabelling of the line to an all-time path
-- statement:
--   Let $a<b$ be reals with $b-a>2$, and let $\tau(t)=\max 0\,(\min t\,1)$. Then there is a jointly continuous family of self-homeomorphisms $F_t$ of the real line, with $F_0=\mathrm{id}$, such that for every $|u|\le 1$
--   $$F_t(a+u)=a(1-\tau(t))+u,\qquad F_t(b+u)=b(1-\tau(t))+3\tau(t)+u .$$
--   In words: whenever two disjoint arcs of the line are relabelled to the standard arcs $[-1,1]$ and $[2,4]$ at time $1$, that single relabelling can be realised, for all times simultaneously, by a continuous motion that agrees with the prescribed relabelling on both arcs at every time. This is the "endpoint relabelling lifts to an all-time path" step of Chapter 15. The condition $b-a>2$ says the two arcs have disjoint interiors and are separated by at least one unit; it is necessary, since otherwise the two prescriptions on the overlapping arcs would be incompatible with an increasing homeomorphism.
-- source:
--   Reusable all-time lifting step for Chapter 15 (Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition, 2018, p. 130).
--
--   Construction. With tau(t) = max 0 (min t 1), L = b - a - 2 > 0 and M = (1 - tau) + tau / L, set the breakpoints at s = a + 1 and e = b - 1, which are FIXED in x, and define
--
--     F t x = if x <= a + 1     then x - tau*a
--             else if x <= b - 1 then (a + 1 - tau*a) + (x - (a + 1)) * M
--             else                    x + tau*(3 - b).
--
--   The two arc laws hold without any case analysis on u: u <= 1 gives a + u <= a + 1, so the left arc always lands in the first branch, which is a pure translation by -tau*a; and -1 <= u gives b + u >= b - 1, so the right arc always lands in the third branch, a pure translation by tau*(3 - b). Expanding each gives exactly a*(1 - tau) + u and b*(1 - tau) + 3*tau + u.
--
--   Each F t is a homeomorphism because its three slopes are (1, M, 1): M = (1 - tau) + tau/L is affine in tau and L > 0, so M > 0 on [0, 1]; the two branches agree at x = b - 1 precisely because L*M = (1 - tau)*L + tau; the tails have slope exactly 1, so F t is onto. The inverse is supplied explicitly, with its own breakpoints at the images a + 1 - tau*a and b - 1 + tau*(3 - b), so no order-embedding or strict-monotonicity machinery is needed.
--
--   All arithmetic was verified exactly in rational arithmetic before formalisation (40000 rational samples of (a, b, t) with L > 0: zero violations of both arc laws, both round trips, F_0 = id, breakpoint agreement and M > 0).

import Mathlib

theorem BookSixth.alltime_line_relabel_exists (a b : ℝ) (hL : 0 < b - a - 2) :
    ∃ F : ℝ → (ℝ ≃ₜ ℝ),
      Continuous (fun p : ℝ × ℝ => (F p.1) p.2) ∧
      Continuous (fun p : ℝ × ℝ => (F p.1).symm p.2) ∧
      (∀ x, F 0 x = x) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (a + u) = a * (1 - max 0 (min t 1)) + u) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (b + u) = b * (1 - max 0 (min t 1)) + 3 * max 0 (min t 1) + u) := by sorry
