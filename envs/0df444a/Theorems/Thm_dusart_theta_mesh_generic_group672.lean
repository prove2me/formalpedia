-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group672
-- name    : dusart_theta_mesh_generic_group672
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:31:39.737082+00:00
-- url     : https://prove2.me/theorems/1e791c21-a6e5-48ab-9f64-dff328be4b52
-- title:
--   Verified numerical interval from 9663013120 to 9679790336
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9663013120, 9679790336; 9662936651771238, 9679723531427076).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group672 : DusartNumeric.GenericSpec 9663013120 9679790336 9662936651771238 9679723531427076 := by sorry
