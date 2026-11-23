-- Prove2me | Theorems.Thm_X25519Dalek_differentialAddAndDouble_192_364
-- name    : X25519Dalek.differentialAddAndDouble_192_364
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-23T19:33:04.253366+00:00
-- url     : https://prove2.me/theorems/55a7eaff-b97a-450c-af4a-21629719793a
-- title:
--   The compiled curve25519-dalek differential_add_and_double, offsets 192–364: the sums and differences of both points, meets its segment contract
-- statement:
--   A segment contract for block 12 of `x25519CliMultiLib` (`curve25519_dalek::montgomery::differential_add_and_double`), offsets 192–364: the sums and differences of both points. For every placeable placement `mpl` and every running state `s` with the library's code loaded, whose program counter, stack pointer, registers and memory are as in the hypotheses (the 1,056-byte stack frame below the entry stack pointer `S` split into 64-bit word lists, the projective points `P` and `Q` and the base point `u1` as word lists whose limbs are below the stated bounds, the constant `121666` read-only, and any frame `F`), execution of the block's program reaches a state `sf` that is running, at the stated program counter and stack pointer, with the callee-saved vector registers unchanged, and, for some 64-bit words, with the stated register contents, memory and facts.
--
--   It completes A and B, computes C = W_Q + U_Q limb by limb and D = U_Q − W_Q (bias and weak reduction), and stores all four in their stack slots. At offset 364, before the first call, the slots hold A, B, C, D with limb bounds and their values mod p, and the argument registers point at A, its output slot and k = 1. Limb bounds are stated as `w.toNat < 2^k` for each limb and values as `fe51Val w0 w1 w2 w3 w4 % p25519`, with the field operations `fpAdd`, `fpSub`, `fpPow` of the mission's definitions.
--
--   This is one of ten consecutive segments into which the proof of `X25519Dalek.fnOk_differential_add_and_double` is split so that each part fits the verifier's limits; the segments, their formulas and the contract follow DeepMind's proof of the block (`differential_add_and_double_ok_of` and `diff_add_mid`, google-deepmind/code-verification @ 8c8d371f, `Shared51/MontgomeryLadderCode1.lean`).
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/MontgomeryLadderCode1.lean, theorems differential_add_and_double_ok_of and diff_add_mid, https://github.com/google-deepmind/code-verification

import Mathlib
import Definitions.Def_X25519Dalek_Spec

set_option maxHeartbeats 4000000

namespace X25519Dalek

theorem differentialAddAndDouble_192_364 {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {t144 t164 b_2 b_3 b_4 t76 t96 t100 a_3 a_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 g1 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 192) (hsp : s.sp = S - 832#64)
    (hr0 : s.regs.regs 0#5 = t120)
    (hr1 : s.regs.regs 1#5 = t68)
    (hr2 : s.regs.regs 2#5 = u1)
    (hr8 : s.regs.regs 8#5 = t188)
    (hr9 : s.regs.regs 9#5 = t172)
    (hr10 : s.regs.regs 10#5 = t176)
    (hr11 : s.regs.regs 11#5 = t180)
    (hr12 : s.regs.regs 12#5 = t144)
    (hr13 : s.regs.regs 13#5 = t156)
    (hr14 : s.regs.regs 14#5 = t168)
    (hr15 : s.regs.regs 15#5 = t160)
    (hr16 : s.regs.regs 16#5 = t100)
    (hr17 : s.regs.regs 17#5 = p8)
    (hr18 : s.regs.regs 18#5 = p9)
    (hr19 : s.regs.regs 19#5 = Qb)
    (hr20 : s.regs.regs 20#5 = Pb)
    (hr21 : s.regs.regs 21#5 = c21)
    (hr22 : s.regs.regs 22#5 = 0x007ffffffffffff0#64)
    (hr23 : s.regs.regs 23#5 = c23)
    (hr24 : s.regs.regs 24#5 = 36028797018963664#64)
    (hr25 : s.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64))
    (hr26 : s.regs.regs 26#5 = c26)
    (hr27 : s.regs.regs 27#5 = c27)
    (hr28 : s.regs.regs 28#5 = c28)
    (hr29 : s.regs.regs 29#5 = (S - 96#64))
    (hr30 : s.regs.regs 30#5 = c30)
    (e68 : t68 = p9 + p4)
    (e72 : t72 = p4 - p9)
    (e76 : t76 = p5 + p0)
    (e80 : t80 = p0 + 36028797018963664#64)
    (e84 : t84 = t72 + 0x007ffffffffffff0#64)
    (e96 : t96 = p6 + p1)
    (e100 : t100 = p7 + p2)
    (e104 : t104 = p1 - p6)
    (e108 : t108 = t84 >>> 51)
    (e112 : t112 = t80 - p5)
    (e120 : t120 = p8 + p3)
    (e124 : t124 = t104 + 0x007ffffffffffff0#64)
    (e132 : t132 = p2 - p7)
    (e136 : t136 = t112 &&& 0x0007ffffffffffff#64)
    (e140 : t140 = p3 - p8)
    (e144 : t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64)
    (e148 : t148 = t132 + 0x007ffffffffffff0#64)
    (e152 : t152 = t124 &&& 0x0007ffffffffffff#64)
    (e156 : t156 = t140 + 0x007ffffffffffff0#64)
    (e160 : t160 = t148 &&& 0x0007ffffffffffff#64)
    (e164 : t164 = t152 + t112 >>> 51)
    (e168 : t168 = t156 &&& 0x0007ffffffffffff#64)
    (e172 : t172 = t160 + t124 >>> 51)
    (e176 : t176 = t84 &&& 0x0007ffffffffffff#64)
    (e180 : t180 = t168 + t148 >>> 51)
    (e188 : t188 = t176 + t156 >>> 51)
    (hs : s.mem ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 364 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ t316 t328 t324 t336 t348 t232 t228 t248 t256 t276 t344 t304 t332 t308 t280 : BitVec 64,
        sf.regs.regs 0#5 = (S - 824#64) ∧
        sf.regs.regs 1#5 = ((((1#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 2#5 = u1 ∧
        sf.regs.regs 8#5 = (S - 664#64) ∧
        sf.regs.regs 9#5 = t348 ∧
        sf.regs.regs 10#5 = t324 ∧
        sf.regs.regs 11#5 = t344 ∧
        sf.regs.regs 12#5 = t304 ∧
        sf.regs.regs 13#5 = t332 ∧
        sf.regs.regs 14#5 = t308 ∧
        sf.regs.regs 15#5 = t280 ∧
        sf.regs.regs 16#5 = q7 ∧
        sf.regs.regs 17#5 = t256 ∧
        sf.regs.regs 18#5 = q8 ∧
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = c21 ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = c23 ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = c26 ∧
        sf.regs.regs 27#5 = c27 ∧
        sf.regs.regs 28#5 = c28 ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        sf.regs.regs 30#5 = c30 ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984)) ∧
        ((t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496) ∧ (fe51Val t316 t328 t324 t336 t348) % p25519 = fpSub ((fe51Val q0 q1 q2 q3 q4) % p25519) ((fe51Val q5 q6 q7 q8 q9) % p25519)) ∧
        ((t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984) ∧ (fe51Val t232 t228 t248 t256 t276) % p25519 = fpAdd ((fe51Val q5 q6 q7 q8 q9) % p25519) ((fe51Val q0 q1 q2 q3 q4) % p25519)) ∧
        ((t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496) ∧ (fe51Val t144 t164 t172 t180 t188) % p25519 = fpSub ((fe51Val p0 p1 p2 p3 p4) % p25519) ((fe51Val p5 p6 p7 p8 p9) % p25519)) ∧
        ((t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984) ∧ (fe51Val t76 t96 t100 t120 t68) % p25519 = fpAdd ((fe51Val p5 p6 p7 p8 p9) % p25519) ((fe51Val p0 p1 p2 p3 p4) % p25519)) ∧
        sf.mem ⊨ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  sorry

end X25519Dalek
