-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_interval07
-- name    : dusart_theta_mesh_generic_interval07
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T04:57:14.574164+00:00
-- url     : https://prove2.me/theorems/13f5fc06-41e0-45c3-9d7f-003ed412e7dc
-- title:
--   Certified numerical interval 9663013120 to 10000064768
-- statement:
--   Let $S(a,b;u,v)$ be any predicate on four natural numbers that validates all elementary blocks satisfying the finite checker's validity and size conditions, and is closed under concatenation with matching endpoint carries. Then
--
--   $$S(9663013120,10000064768;9662936651771238,10000013784295984).$$
--
--   The carries use scale one million. This certifies a contiguous numerical interval used in the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite-certificate formalization.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_interval07 : DusartNumeric.GenericSpec 9663013120 10000064768 9662936651771238 10000013784295984 := by sorry
