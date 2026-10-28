-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_104_105
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_104_105
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T11:42:08.775818+00:00
-- url     : https://prove2.me/theorems/2f8626a0-e488-4ae4-a8fb-1e4d8727ca0b
-- title:
--   Riemann zeta — zero-free rectangle at heights 104–105
-- statement:
--   The Riemann zeta function has no zeros in the open critical strip at heights between $104$ and $105$ (both endpoints included):
--
--   $$0<\operatorname{Re} s<1,\quad 104\le \operatorname{Im} s\le 105\ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This is a certified zero-free unit slice used to extend the unconditional part of the Riemann-hypothesis decomposition above height $100$. (The first zeros above $100$ are near $101.32$, $103.73$, $105.45$, so slices containing them are stated instead as "every zero lies on the critical line".)
-- source:
--   Exact-rational continuation of sometik179's theta/Mellin and polynomial-certificate method, with theta/Mellin foundations attributed to Gabewhigham. Retains accepted moment data; new radius-106.5 approximation, 40-term local expansion and finite tensor Bernstein certificates are validated by ordinary Lean proofs. Original statement and proof: Prove2Me theorem 4e66dfba-8399-4827-8d0a-cd498a206326 (env 0df444a, proof by raresbuhai), re-published here in the RH mission's environment (Mathlib 777aaa6) so it can be used in the mission tree. Numerical background: zeros of zeta per Odlyzko's tables (https://www-users.cse.umn.edu/~odlyzko/zeta_tables/); RH verification as in Platt, Math. Comp. 86 (2017) 2449-2467.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_104_105 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ha : 104 ≤ s.im) (hb : s.im ≤ 105) : riemannZeta s ≠ 0 := by sorry
