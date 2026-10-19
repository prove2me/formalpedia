-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group136
-- name    : dusart_theta_mesh_generic_group136
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:29:02.407126+00:00
-- url     : https://prove2.me/theorems/a14a50f8-b637-494b-9495-f62966a20c8b
-- title:
--   Verified numerical interval from 737534208 to 745922816
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(737534208, 745922816; 737506337178899, 745897095208335).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group136 : DusartNumeric.GenericSpec 737534208 745922816 737506337178899 745897095208335 := by sorry
