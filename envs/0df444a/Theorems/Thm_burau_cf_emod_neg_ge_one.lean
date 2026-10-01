-- Prove2me | Theorems.Thm_burau_cf_emod_neg_ge_one
-- name    : burau_cf_emod_neg_ge_one
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:59:06.151384+00:00
-- url     : https://prove2.me/theorems/4b49d480-20bf-4f55-8c2f-958b927f8ac2
-- title:
--   Negative reciprocal: first step of the Euclidean descent (remainder)
-- statement:
--   **First step of the negative-reciprocal rule of continued fractions (remainder form).**
--   For $a>0$ and $b/a\ge 1$,
--   $$ (-a)\bmod b = b-a , $$
--   the companion of $(-a)/b=-1$. Together they show that the standard Euclidean descent applied to the
--   pair $(b,-a)$ takes the explicit step $(b,-a)\mapsto(b-a,b)$, the pivot of the analysis of the
--   transformation $x\mapsto-1/x$ of continued fractions.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Mathlib

set_option autoImplicit false

theorem burau_cf_emod_neg_ge_one (a b : ℤ) (ha : 0 < a) (h : 1 ≤ b / a) :
    (-a) % b = b - a := by sorry
