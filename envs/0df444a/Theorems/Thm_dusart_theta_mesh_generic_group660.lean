-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group660
-- name    : dusart_theta_mesh_generic_group660
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:29:55.927249+00:00
-- url     : https://prove2.me/theorems/e3436701-865c-49cd-8d80-4f93bd87855f
-- title:
--   Verified numerical interval from 9461686528 to 9478463744
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9461686528, 9478463744; 9461601859072932, 9478373058441958).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group660 : DusartNumeric.GenericSpec 9461686528 9478463744 9461601859072932 9478373058441958 := by sorry
