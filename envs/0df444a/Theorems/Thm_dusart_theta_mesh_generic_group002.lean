-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group002
-- name    : dusart_theta_mesh_generic_group002
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:05:13.901359+00:00
-- url     : https://prove2.me/theorems/89885e68-e384-464b-8864-9887778d809b
-- title:
--   Verified numerical interval from 104194304 to 106291456
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(104194304, 106291456; 104186846574220, 106282121086858).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group002 : DusartNumeric.GenericSpec 104194304 106291456 104186846574220 106282121086858 := by sorry
