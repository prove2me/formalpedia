-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group240
-- name    : dusart_theta_mesh_generic_group240
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:40:19.18672+00:00
-- url     : https://prove2.me/theorems/2fd62efe-ace2-45b5-bbc9-9946063c1cae
-- title:
--   Verified numerical interval from 2415255808 to 2432033024
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(2415255808, 2432033024; 2415200123007171, 2431981220726353).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group240 : DusartNumeric.GenericSpec 2415255808 2432033024 2415200123007171 2431981220726353 := by sorry
