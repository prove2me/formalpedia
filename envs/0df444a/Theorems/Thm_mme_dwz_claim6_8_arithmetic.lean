-- Prove2me | Theorems.Thm_mme_dwz_claim6_8_arithmetic
-- name    : mme_dwz_claim6_8_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T09:05:54.770571+00:00
-- url     : https://prove2.me/theorems/e1127caa-55ff-42a3-af31-98afe5486b3a
-- title:
--   Claim 6.8: the asymmetric modulus bounds the collision ratio by one eighth
-- statement:
--   Let $N_\alpha$ and $p_{\mathrm{comp}}$ be nonnegative real numbers, and let $N_{BZ}$ and $M$ be positive. If the asymmetric-hashing modulus satisfies
--
--   $$
--   M\ge \frac{8N_\alpha p_{\mathrm{comp}}}{N_{BZ}},
--   $$
--
--   then the collision ratio obeys
--
--   $$
--   \frac{N_\alpha p_{\mathrm{comp}}}{N_{BZ}M}\le \frac18.
--   $$
--
--   This is the deterministic final inequality in the proof of Duan--Wu--Zhou Claim 6.8. The preceding probabilistic argument must separately bound the hole probability by the displayed collision ratio; this theorem isolates only the exact arithmetic implication used after that bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Claim 6.8 and its final displayed calculation on Section 6.2, printed p. 56; https://arxiv.org/abs/2210.10173.

import Mathlib.Tactic

theorem mme_dwz_claim6_8_arithmetic
    (Nalpha NBZ pcomp M : ℝ)
    (hNalpha : 0 ≤ Nalpha) (hpcomp : 0 ≤ pcomp)
    (hNBZ : 0 < NBZ) (hM : 0 < M)
    (hmodulus : 8 * Nalpha * pcomp / NBZ ≤ M) :
    Nalpha * pcomp / (NBZ * M) ≤ 1 / 8 := by sorry
