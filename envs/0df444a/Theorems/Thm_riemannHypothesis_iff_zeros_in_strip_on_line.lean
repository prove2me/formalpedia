-- Prove2me | Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
-- name    : riemannHypothesis_iff_zeros_in_strip_on_line
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T16:12:56.153301+00:00
-- url     : https://prove2.me/theorems/7a32a59d-8f64-4ff0-96c4-f90c9549b1fd
-- title:
--   Mathlib RH is equivalent to its open critical-strip formulation
-- statement:
--   For Mathlib’s Riemann zeta function, the Riemann hypothesis stated for all zeros except the negative even integers and the point 1 is equivalent to the following open-strip statement: for every complex s with zeta(s)=0 and 0<Re(s)<1, one has Re(s)=1/2. This theorem identifies the two formulations; it does not prove the Riemann hypothesis. The nontrivial-zero location theorem is used in the global direction, and the strict strip inequalities exclude negative even integers and 1 in the reverse direction.
-- source:
--   monocap-tech/weil, native compiling commit e348db588b5acb95a2bf9bf73bc9a10890c3f92e, WeilDefect/Arithmetic/ZetaZeroLocation.lean, riemannHypothesis_iff_zeros_in_strip_on_line; proof uses existing P2M Kawahira.nontrivial_zero_mem_strip (1c05c2d2-ba60-405b-8ae6-436f660af859).

import Mathlib.NumberTheory.LSeries.Nonvanishing
set_option autoImplicit false
open Complex

theorem riemannHypothesis_iff_zeros_in_strip_on_line :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by sorry
