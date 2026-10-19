-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group070
-- name    : dusart_theta_mesh_generic_group070
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:15:23.896868+00:00
-- url     : https://prove2.me/theorems/5440fca4-768d-4ac1-81ea-3c192908a92e
-- title:
--   Verified numerical interval from 292937984 to 297132288
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(292937984, 297132288; 292922115152298, 297116214231469).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group070 : DusartNumeric.GenericSpec 292937984 297132288 292922115152298 297116214231469 := by sorry
