-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group678
-- name    : dusart_theta_mesh_generic_group678
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:32:31.357481+00:00
-- url     : https://prove2.me/theorems/e800ce2f-3519-4f71-9257-3eac4283ea3e
-- title:
--   Verified numerical interval from 9763676416 to 9780453632
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9763676416, 9780453632; 9763621668972664, 9780401294627483).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group678 : DusartNumeric.GenericSpec 9763676416 9780453632 9763621668972664 9780401294627483 := by sorry
