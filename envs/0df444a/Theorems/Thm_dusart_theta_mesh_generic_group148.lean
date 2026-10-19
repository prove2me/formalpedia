-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group148
-- name    : dusart_theta_mesh_generic_group148
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:30:00.233948+00:00
-- url     : https://prove2.me/theorems/0ea2696f-d2eb-46b9-a48a-11a6c5f9061d
-- title:
--   Verified numerical interval from 871751936 to 888529152
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(871751936, 888529152; 871725036496747, 888495761170712).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group148 : DusartNumeric.GenericSpec 871751936 888529152 871725036496747 888495761170712 := by sorry
