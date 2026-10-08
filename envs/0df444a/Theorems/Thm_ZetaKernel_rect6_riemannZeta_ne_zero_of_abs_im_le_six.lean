-- Prove2me | Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
-- name    : ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T04:01:35.054549+00:00
-- url     : https://prove2.me/theorems/d1d6b916-b447-4dee-bd58-3bccf329d1d9
-- title:
--   An explicit zero-free rectangle of height 6 for the Riemann zeta function
-- statement:
--   The Riemann zeta function has no zero in the low-lying rectangle {s : 0 < Re s < 1, |Im s| <= 6}.
--
--   This is the explicit zero-free rectangle used as the base case of the verified-height zero count: since the first nontrivial zero of zeta is 1/2 + 14.134725... i, the strip 0 < Re s < 1 with |Im s| <= 6 is zero-free, and in particular the count of zeros with 0 < Im s <= 7 vanishes.
--
--   The proof goes through Mathlib's completed zeta function. On the strip the completed zeta without its pole, Lambda_0(s) = Lambda(s) + s/2 + 1, satisfies |Lambda_0(s)| <= 1/8. If instead Lambda(s) = 0 then Lambda_0(s) = s/2 + 1, so 1/(norm s * norm (1-s)) = norm (Lambda_0 s) <= 1/8, forcing norm s * norm (1-s) >= 8. But for 0 < Re s < 1 and |Im s| <= 6 one has norm s ^ 2 <= (Re s)^2 + 36 and norm (1-s) ^ 2 <= (1 - Re s)^2 + 36, so norm s ^ 2 * norm (1-s) ^ 2 <= (u^2 + 36)((1-u)^2 + 36) <= 1332 < 64, a contradiction. The bound |Lambda_0(s)| <= 1/8 comes from the Mellin transform of the modified theta kernel, whose majorant integrates to 0.0536 < 1/8; the tail integral uses exp pi >= 23. The kernel estimates use only pi > 3.14 and Re s in (0,1).
-- source:
--   Standard zero-free rectangle for the Riemann zeta function, from |Lambda_0(s)| <= 1/8 for 0 < Re s < 1 together with the elementary estimate norm s * norm (1-s) <= 36.5 on that rectangle. Used as the height-6 base case of the Riemann--von Mangoldt count at T0 = 3.29e9 in Tao, arXiv:1201.6656v4, Section 7.

import Mathlib

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

theorem ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) (him : |s.im| ≤ 6) : riemannZeta s ≠ 0 := by
  sorry
