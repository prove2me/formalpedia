-- Prove2me | Theorems.Thm_mme_dwz_q6_table2_022_profile_entropy_identity
-- name    : mme_dwz_q6_table2_022_profile_entropy_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:03:04.086462+00:00
-- url     : https://prove2.me/theorems/2ef26fe4-932c-4de4-9b06-dd571d7ae59f
-- title:
--   Exact entropy base of the Table-2 022/202 split profile
-- statement:
--   Let $a=3477403/10^8$ and $g=1-2a=93045194/10^8$, the three-way split used for the $022$ and $202$ constituents in the DWZ Table-2 certificate. For the probability profile $p=(a,g,a)$, prove the exact identity
--
--   $$
--   2^{H(p)}=rac{1}{a^{2a}g^g}.
--   $$
--
--   This identifies the exponential multinomial entropy rate of the finite prescribed-word construction with the scalar normalization appearing in the common component base at indices $9$ and $10$. It is an exact real identity, not a numerical approximation or an asymptotic claim.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173. The entropy expansion itself is the standard multinomial entropy identity.

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data

open MME.DWZSquare

set_option autoImplicit false

theorem mme_dwz_q6_table2_022_profile_entropy_identity :
    let a : ℝ := splitA
    let g : ℝ := 1 - 2 * a
    let profile : Fin 3 → ℝ := ![a, g, a]
    Real.exp (Real.log 2 * mme_modern_entropyBits profile) =
      1 / (Real.rpow a (2 * a) * Real.rpow g g) := by
  sorry
