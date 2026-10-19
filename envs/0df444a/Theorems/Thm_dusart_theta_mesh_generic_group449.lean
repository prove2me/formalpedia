-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group449
-- name    : dusart_theta_mesh_generic_group449
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:07.83888+00:00
-- url     : https://prove2.me/theorems/c9cd33b6-826f-4b2e-863d-1e880632ea3c
-- title:
--   Verified numerical interval from 5921693952 to 5938471168
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5921693952, 5938471168; 5921613235285986, 5938396590954629).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group449 : DusartNumeric.GenericSpec 5921693952 5938471168 5921613235285986 5938396590954629 := by sorry
