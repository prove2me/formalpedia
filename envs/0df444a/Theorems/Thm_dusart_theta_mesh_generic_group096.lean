-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group096
-- name    : dusart_theta_mesh_generic_group096
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:26:18.161469+00:00
-- url     : https://prove2.me/theorems/06b585da-4588-460f-b9fc-56bc138a1694
-- title:
--   Verified numerical interval from 401989888 to 410378496
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(401989888, 410378496; 401971882499010, 410358576532437).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group096 : DusartNumeric.GenericSpec 401989888 410378496 401971882499010 410358576532437 := by sorry
