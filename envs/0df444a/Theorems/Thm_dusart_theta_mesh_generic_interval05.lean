-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_interval05
-- name    : dusart_theta_mesh_generic_interval05
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T04:57:15.291009+00:00
-- url     : https://prove2.me/theorems/24c46287-9f7e-41e6-882f-b76a1164a8a7
-- title:
--   Certified numerical interval 6441787648 to 8052400384
-- statement:
--   Let $S(a,b;u,v)$ be any predicate on four natural numbers that validates all elementary blocks satisfying the finite checker's validity and size conditions, and is closed under concatenation with matching endpoint carries. Then
--
--   $$S(6441787648,8052400384;6441698088936622,8052306946255057).$$
--
--   The carries use scale one million. This certifies a contiguous numerical interval used in the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite-certificate formalization.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_interval05 : DusartNumeric.GenericSpec 6441787648 8052400384 6441698088936622 8052306946255057 := by sorry
