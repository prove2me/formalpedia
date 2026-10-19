-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group692
-- name    : dusart_theta_mesh_generic_group692
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:34:15.533875+00:00
-- url     : https://prove2.me/theorems/8d82c73f-c40e-44b3-93c6-f8bc2bbf965a
-- title:
--   Verified numerical interval from 9998557440 to 10000064768
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9998557440, 10000064768; 9998509278974729, 10000013784295984).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group692 : DusartNumeric.GenericSpec 9998557440 10000064768 9998509278974729 10000013784295984 := by sorry
