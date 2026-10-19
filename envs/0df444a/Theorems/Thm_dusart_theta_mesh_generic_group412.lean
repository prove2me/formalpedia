-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group412
-- name    : dusart_theta_mesh_generic_group412
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:59:34.318977+00:00
-- url     : https://prove2.me/theorems/f234340e-4f72-4779-96d6-8109b16b8b3a
-- title:
--   Verified numerical interval from 5300936960 to 5317714176
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5300936960, 5317714176; 5300877885913158, 5317647812683125).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group412 : DusartNumeric.GenericSpec 5300936960 5317714176 5300877885913158 5317647812683125 := by sorry
