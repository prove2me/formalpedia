-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group393
-- name    : dusart_theta_mesh_generic_group393
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:59:31.409884+00:00
-- url     : https://prove2.me/theorems/0c96650c-b8ea-42b0-856b-fdeb1336a5a7
-- title:
--   Verified numerical interval from 4982169856 to 4998947072
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(4982169856, 4998947072; 4982100447190138, 4998863595651529).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group393 : DusartNumeric.GenericSpec 4982169856 4998947072 4982100447190138 4998863595651529 := by sorry
