-- Prove2me | Theorems.Thm_ZetaNine_irrational_zeta_nine
-- name    : ZetaNine.irrational_zeta_nine
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-24T13:15:38.397538+00:00
-- url     : https://prove2.me/theorems/523f37b8-ae98-406c-a3f7-43aa8e002dd7
-- title:
--   Irrationality of ζ(9)
-- statement:
--   The real part of the Riemann zeta function at the complex number 9 is irrational. At this positive integer it is the classical real value ζ(9)=∑_{k≥1}k^(−9). This is the open mission goal.
-- source:
--   Classical open single-value irrationality problem; see W. Zudilin, Arithmetic of linear forms involving odd zeta values, arXiv:math/0206176, and local ζ(9) roadmap/DAG.md §J to root.

import Mathlib

namespace ZetaNine

theorem irrational_zeta_nine :
    Irrational ((riemannZeta (9 : ℂ)).re) := by sorry

end ZetaNine
