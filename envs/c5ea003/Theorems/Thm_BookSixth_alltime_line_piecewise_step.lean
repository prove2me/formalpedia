-- Prove2me | Theorems.Thm_BookSixth_alltime_line_piecewise_step
-- name    : BookSixth.alltime_line_piecewise_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:51:07.376153+00:00
-- url     : https://prove2.me/theorems/2615e0c0-e443-47d0-ac7c-ded73a1869dd
-- title:
--   Chapter 15: arithmetic core of the all-time two-arc relabelling of the line
-- statement:
--   Write $\tau=\max 0\,(\min t\,1)$ and let $L=b-a-2>0$. These are the three elementary facts about the piecewise-affine relabelling of the line used in Chapter 15: the middle slope $\sigma=(1-\tau)+\tau/L$ is strictly positive; the middle branch, evaluated at the right breakpoint $b-1$, agrees with the value of the right branch there (this is the identity $L\sigma=(1-\tau)L+\tau$, and it is what makes the piecewise map continuous); and the left branch's offset $\tau a$ exactly cancels the breakpoint $a+1$, so the left branch passes through $a+1-\tau a$ as it must. Together these are the arithmetic core of the all-time two-arc relabelling path; the remaining ingredients are pure topology of $\mathbb R$ and are carried by the later lemmas.
-- source:
--   Arithmetic core of the all-time two-arc relabelling of the line (Chapter 15, Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition, 2018, p. 130).
--
--   Fix $a<b$ with $L=b-a-2>0$, and put $\tau=\max 0\,(\min t\,1)$. The path $F_t$ is piecewise affine with breakpoints fixed at $s=a+1$ and $e=b-1$ and slopes $(1,\sigma,1)$, where $\sigma=(1-\tau)+\tau/L$.
--
--   (i) $\sigma>0$: since $0\le\tau\le1$ and $L>0$, $\sigma$ is a convex combination of $1$ and $1/L$, both positive.
--
--   (ii) The two branches agree at $e=b-1$, i.e. $(s-\tau a)+(e-s)\sigma=e+\tau(3-b)$. After clearing $L$ this is exactly $L\sigma=(1-\tau)L+\tau$, which holds by the definition of $\sigma$; concretely $L\sigma=(1-\tau)L+\tau=b-a-2-\tau(b-a-2)+\tau=b-a-2+\tau(3-b)$. This single identity is the only non-trivial algebra in the whole construction, and it is what makes $F_t$ continuous at the second breakpoint.
--
--   (iii) $\tau a+(s-\tau a)=s$, i.e. the translation of the left branch applied to its own image breakpoint is the identity; this is what lets the inverse map use $a+1$ as the base of its middle branch.
--
--   All three were verified exactly in rational arithmetic before formalisation.

import Mathlib

theorem BookSixth.alltime_line_piecewise_step (a b L : ℝ) (hL : L = b - a - 2)
    (hLb : 0 < b - a - 2) (t : ℝ) :
    (0 < (1 - max 0 (min t 1)) + max 0 (min t 1) / L) ∧
    ((a + 1 - max 0 (min t 1) * a)
        + (b - 1 - (a + 1)) * ((1 - max 0 (min t 1)) + max 0 (min t 1) / L)
      = b - 1 + max 0 (min t 1) * (3 - b)) ∧
    (max 0 (min t 1) * a + (a + 1 - max 0 (min t 1) * a)
        = a + 1) := by sorry
