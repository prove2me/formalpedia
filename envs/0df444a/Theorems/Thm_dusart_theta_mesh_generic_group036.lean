-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group036
-- name    : dusart_theta_mesh_generic_group036
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:12:00.385091+00:00
-- url     : https://prove2.me/theorems/2c0b858d-6465-4467-83cb-e97cea54f22a
-- title:
--   Verified numerical interval from 175497472 to 177594624
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(175497472, 177594624; 175490025176949, 177588190145972).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group036 : DusartNumeric.GenericSpec 175497472 177594624 175490025176949 177588190145972 := by sorry
