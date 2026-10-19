-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group042
-- name    : dusart_theta_mesh_generic_group042
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:12:30.757218+00:00
-- url     : https://prove2.me/theorems/ba8ad740-15b3-4cfb-895c-6c8351ee6aa9
-- title:
--   Verified numerical interval from 188080384 to 190177536
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(188080384, 190177536; 188074101731097, 190170078116059).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group042 : DusartNumeric.GenericSpec 188080384 190177536 188074101731097 190170078116059 := by sorry
