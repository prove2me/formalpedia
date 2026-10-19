-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group301
-- name    : dusart_theta_mesh_generic_group301
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:46:39.056546+00:00
-- url     : https://prove2.me/theorems/f8a9bd2e-ede3-42d4-b225-3e301cff32eb
-- title:
--   Verified numerical interval from 3438665984 to 3455443200
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(3438665984, 3455443200; 3438590005932055, 3455372801348726).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group301 : DusartNumeric.GenericSpec 3438665984 3455443200 3438590005932055 3455372801348726 := by sorry
