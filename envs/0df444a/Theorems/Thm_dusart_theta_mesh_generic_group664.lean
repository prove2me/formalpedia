-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group664
-- name    : dusart_theta_mesh_generic_group664
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:32:58.099065+00:00
-- url     : https://prove2.me/theorems/4e6fbf62-4486-493a-95bc-6715324c108c
-- title:
--   Verified numerical interval from 9528795392 to 9545572608
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9528795392, 9545572608; 9528702328632904, 9545474271302836).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group664 : DusartNumeric.GenericSpec 9528795392 9545572608 9528702328632904 9545474271302836 := by sorry
