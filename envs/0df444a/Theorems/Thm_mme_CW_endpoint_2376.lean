-- Prove2me | Theorems.Thm_mme_CW_endpoint_2376
-- name    : mme_CW_endpoint_2376
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T23:39:02.741837+00:00
-- url     : https://prove2.me/theorems/f1176c0b-c3ed-4417-82fe-77371e17d67c
-- title:
--   The auxiliary inequality forces omega below 2.376
-- statement:
--   Let $w$ be a real exponent parameter. At $q=6$, use the exact normalized Coppersmith--Winograd parameters $a,b,c,d$. If the Section 8 auxiliary expression satisfies $$\operatorname{auxiliaryRHS}(6,w/3,a,b,c,d)\le64,$$ then $$w<\frac{297}{125}=2.376.$$ The proof combines monotonicity in $\tau$ with the strict exact certificate at $\tau=99/125$: at that endpoint the same expression is greater than $64$. Thus this theorem isolates the analytic and numerical endpoint from the combinatorial laser extraction.
-- source:
--   Exact rational consequence of the normalized auxiliary equation and numerical parameters in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 269 (PDF p. 19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
open MME

theorem mme_CW_endpoint_2376
    (w : ℝ)
    (haux :
      auxiliaryRHS 6 (w / 3) cw2376_a cw2376_b cw2376_c cw2376_d ≤ 64) :
    w < 297 / 125 := by sorry
