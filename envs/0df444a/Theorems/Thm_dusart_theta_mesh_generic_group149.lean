-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group149
-- name    : dusart_theta_mesh_generic_group149
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T01:29:59.770894+00:00
-- url     : https://prove2.me/theorems/c699fe6a-a7ce-4985-ab69-42c52042bc1e
-- title:
--   Verified numerical interval from 888529152 to 905306368
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(888529152, 905306368; 888495761170712, 905262834830659).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group149 : DusartNumeric.GenericSpec 888529152 905306368 888495761170712 905262834830659 := by sorry
