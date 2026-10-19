-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group324
-- name    : dusart_theta_mesh_generic_group324
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:49:11.266001+00:00
-- url     : https://prove2.me/theorems/218d76c3-6215-4aac-a5bb-96bc6c7ce184
-- title:
--   Verified numerical interval from 3824541952 to 3841319168
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3824541952, 3841319168; 3824515489950870, 3841293447078903).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group324 : DusartNumeric.GenericSpec 3824541952 3841319168 3824515489950870 3841293447078903 := by sorry
