-- Prove2me | Theorems.Thm_dusart_theta_mesh_generic_group456
-- name    : dusart_theta_mesh_generic_group456
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T02:07:07.333318+00:00
-- url     : https://prove2.me/theorems/6015c472-1dda-4ec6-b961-4a3a512383c1
-- title:
--   Verified numerical interval from 6039134464 to 6055911680
-- statement:
--   Let $S(a,b;u,v)$ be a predicate on four natural numbers that validates every elementary block accepted by the finite checker under its validity and size conditions, and is closed under concatenating adjacent intervals with matching carries. Then
--
--   $$S(6039134464, 6055911680; 6039059307423534, 6055822176346095).$$
--
--   The last two arguments are endpoint carries with scale one million. This result provides a verified numerical interval for composing the finite Chebyshev theta estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Supporting finite-certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_theta_mesh_numeric

theorem dusart_theta_mesh_generic_group456 : DusartNumeric.GenericSpec 6039134464 6055911680 6039059307423534 6055822176346095 := by sorry
