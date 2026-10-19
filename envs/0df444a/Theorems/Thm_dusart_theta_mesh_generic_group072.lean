-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group072
-- name    : dusart_theta_mesh_generic_group072
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:24:52.175404+00:00
-- url     : https://prove2.me/theorems/ab3a7dd7-32a9-43aa-8688-c9fe1c8ae9ba
-- title:
--   Verified numerical interval from 301326592 to 305520896
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(301326592, 305520896; 301312452401436, 305503987964008).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group072 : DusartNumeric.GenericSpec 301326592 305520896 301312452401436 305503987964008 := by sorry
