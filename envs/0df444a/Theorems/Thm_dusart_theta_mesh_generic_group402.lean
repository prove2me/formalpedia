-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group402
-- name    : dusart_theta_mesh_generic_group402
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:58:31.421681+00:00
-- url     : https://prove2.me/theorems/a2b97292-3e1e-42cd-9e75-51e4075e2a57
-- title:
--   Verified numerical interval from 5133164800 to 5149942016
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(5133164800, 5149942016; 5133086539280327, 5149866295198825).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group402 : DusartNumeric.GenericSpec 5133164800 5149942016 5133086539280327 5149866295198825 := by sorry
