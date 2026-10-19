-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group107
-- name    : dusart_theta_mesh_generic_group107
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:27:27.459366+00:00
-- url     : https://prove2.me/theorems/db0a234d-791d-41a1-ab2a-1512260368b2
-- title:
--   Verified numerical interval from 494264576 to 502653184
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(494264576, 502653184; 494249080063817, 502634065851743).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group107 : DusartNumeric.GenericSpec 494264576 502653184 494249080063817 502634065851743 := by sorry
