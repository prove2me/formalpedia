-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group052
-- name    : dusart_theta_mesh_generic_group052
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:13:52.7105+00:00
-- url     : https://prove2.me/theorems/76e80542-3d9d-4929-9b65-b68269227d95
-- title:
--   Verified numerical interval from 217440512 to 221634816
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(217440512, 221634816; 217426794495484, 221616182447770).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group052 : DusartNumeric.GenericSpec 217440512 221634816 217426794495484 221616182447770 := by sorry
