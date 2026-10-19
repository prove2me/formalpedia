-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group030
-- name    : dusart_theta_mesh_generic_group030
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:11:46.006768+00:00
-- url     : https://prove2.me/theorems/905a4b9f-0746-48be-9047-98d94dc54504
-- title:
--   Verified numerical interval from 162914560 to 165011712
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(162914560, 165011712; 162900023398825, 164999456331067).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group030 : DusartNumeric.GenericSpec 162914560 165011712 162900023398825 164999456331067 := by sorry
