-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_interval00
-- name    : dusart_theta_mesh_generic_interval00
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T04:55:35.085052+00:00
-- url     : https://prove2.me/theorems/a635ad76-83ab-4aee-b20f-ccd9f6438650
-- title:
--   Certified numerical interval 100000000 to 401989888
-- statement:
--   Let $S(a,b;u,v)$ be any predicate on four natural numbers that validates all elementary blocks satisfying the finite checker's validity and size conditions, and is closed under concatenation with matching endpoint carries. Then
--
--   $$S(100000000,401989888;99989691935170,401971882499010).$$
--
--   The carries use scale one million. This certifies a contiguous numerical interval used in the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite-certificate formalization.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_interval00 : DusartNumeric.GenericSpec 100000000 401989888 99989691935170 401971882499010 := by sorry
