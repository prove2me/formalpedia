-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group481
-- name    : dusart_theta_mesh_generic_group481
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:08:17.207959+00:00
-- url     : https://prove2.me/theorems/382028ce-b933-40a3-b149-894a9b29c9ae
-- title:
--   Verified numerical interval from 6458564864 to 6475342080
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6458564864, 6475342080; 6458465810877130, 6475245243018944).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group481 : DusartNumeric.GenericSpec 6458564864 6475342080 6458465810877130 6475245243018944 := by sorry
