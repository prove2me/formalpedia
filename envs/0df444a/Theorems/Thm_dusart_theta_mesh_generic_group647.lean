-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group647
-- name    : dusart_theta_mesh_generic_group647
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:31:15.852824+00:00
-- url     : https://prove2.me/theorems/2d8eb987-872a-4209-88e1-6aa0b1fac587
-- title:
--   Verified numerical interval from 9243582720 to 9260359936
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(9243582720, 9260359936; 9243480414236856, 9260257114797993).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group647 : DusartNumeric.GenericSpec 9243582720 9260359936 9243480414236856 9260257114797993 := by sorry
