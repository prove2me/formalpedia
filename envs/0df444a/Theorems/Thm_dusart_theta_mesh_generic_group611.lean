-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group611
-- name    : dusart_theta_mesh_generic_group611
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:25:03.80591+00:00
-- url     : https://prove2.me/theorems/a4190778-bbc7-4b8a-8512-7ba05dc7978b
-- title:
--   Verified numerical interval from 8639602944 to 8656380160
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8639602944, 8656380160; 8639535176784722, 8656310595611643).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group611 : DusartNumeric.GenericSpec 8639602944 8656380160 8639535176784722 8656310595611643 := by sorry
