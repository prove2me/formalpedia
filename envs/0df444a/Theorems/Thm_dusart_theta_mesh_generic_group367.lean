-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group367
-- name    : dusart_theta_mesh_generic_group367
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:54:13.43261+00:00
-- url     : https://prove2.me/theorems/a5094b18-a9df-483f-9e67-984fbbf456cf
-- title:
--   Verified numerical interval from 4545962240 to 4562739456
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4545962240, 4562739456; 4545896026981128, 4562674648614151).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group367 : DusartNumeric.GenericSpec 4545962240 4562739456 4545896026981128 4562674648614151 := by sorry
