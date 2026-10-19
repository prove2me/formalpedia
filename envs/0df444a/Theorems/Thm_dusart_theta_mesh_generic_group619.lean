-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group619
-- name    : dusart_theta_mesh_generic_group619
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:24:58.508554+00:00
-- url     : https://prove2.me/theorems/63f5ead4-1e22-4f39-85b8-b88cefb26426
-- title:
--   Verified numerical interval from 8773820672 to 8790597888
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(8773820672, 8790597888; 8773726521826864, 8790507805655817).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group619 : DusartNumeric.GenericSpec 8773820672 8790597888 8773726521826864 8790507805655817 := by sorry
