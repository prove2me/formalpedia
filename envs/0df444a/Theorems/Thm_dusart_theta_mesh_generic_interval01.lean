-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_interval01
-- name    : dusart_theta_mesh_generic_interval01
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T04:55:35.257444+00:00
-- url     : https://prove2.me/theorems/26473cf6-01d8-40a3-97c6-2d5988833af5
-- title:
--   Certified numerical interval 401989888 to 1609949440
-- statement:
--   Let $S(a,b;u,v)$ be any predicate on four natural numbers that validates all elementary blocks satisfying the finite checker's validity and size conditions, and is closed under concatenation with matching endpoint carries. Then
--
--   $$S(401989888,1609949440;401971882499010,1609919129810472).$$
--
--   The carries use scale one million. This certifies a contiguous numerical interval used in the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite-certificate formalization.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_interval01 : DusartNumeric.GenericSpec 401989888 1609949440 401971882499010 1609919129810472 := by sorry
