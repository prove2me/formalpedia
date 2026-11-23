-- Prove2me | Theorems.Thm_X25519Dalek_differentialAddAndDouble_0_192
-- name    : X25519Dalek.differentialAddAndDouble_0_192
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:33:05.13673+00:00
-- url     : https://prove2.me/theorems/25f37767-c48d-4458-aeac-9eede3ac9716
-- title:
--   The compiled curve25519-dalek differential_add_and_double, offsets 0–192: the prologue and the sums and differences of the first point, meets its segment contract
-- statement:
--   A segment contract for block 12 of `x25519CliMultiLib` (`curve25519_dalek::montgomery::differential_add_and_double`), offsets 0–192: the prologue and the sums and differences of the first point. For every placeable placement `mpl` and every running state `s` with the library's code loaded, whose program counter, stack pointer, registers and memory are as in the hypotheses (the 1,056-byte stack frame below the entry stack pointer `S` split into 64-bit word lists, the projective points `P` and `Q` and the base point `u1` as word lists whose limbs are below the stated bounds, the constant `121666` read-only, and any frame `F`), execution of the block's program reaches a state `sf` that is running, at the stated program counter and stack pointer, with the callee-saved vector registers unchanged, and, for some 64-bit words, with the stated register contents, memory and facts.
--
--   It saves the callee-saved registers, reserves the frame, stores the pointer u1, and starts computing, from the limbs of P = (U_P : W_P), the sum A = W_P + U_P limb by limb and the biased difference with weak reduction B = U_P − W_P; at offset 192 part of these limbs is in registers and part on the stack, and the conclusion records each computed word by its defining equation (one equation per instruction). Limb bounds are stated as `w.toNat < 2^k` for each limb and values as `fe51Val w0 w1 w2 w3 w4 % p25519`, with the field operations `fpAdd`, `fpSub`, `fpPow` of the mission's definitions.
--
--   This is one of ten consecutive segments into which the proof of `X25519Dalek.fnOk_differential_add_and_double` is split so that each part fits the verifier's limits; the segments, their formulas and the contract follow DeepMind's proof of the block (`differential_add_and_double_ok_of` and `diff_add_mid`, google-deepmind/code-verification @ 8c8d371f, `Shared51/MontgomeryLadderCode1.lean`).
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/MontgomeryLadderCode1.lean, theorems differential_add_and_double_ok_of and diff_add_mid, https://github.com/google-deepmind/code-verification

import Mathlib
import Definitions.Def_X25519Dalek_Spec

set_option maxHeartbeats 4000000

namespace X25519Dalek

theorem differentialAddAndDouble_0_192 {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 g0 g1 a_0 a_1 a_2 a_3 a_4 b_0 b_1 b_2 b_3 b_4 c_0 c_1 c_2 c_3 c_4 d_0 d_1 d_2 d_3 d_4 aa_0 aa_1 aa_2 aa_3 aa_4 bb_0 bb_1 bb_2 bb_3 bb_4 e_0 e_1 e_2 e_3 e_4 da_0 da_1 da_2 da_3 da_4 cb_0 cb_1 cb_2 cb_3 cb_4 sum_0 sum_1 sum_2 sum_3 sum_4 diff_0 diff_1 diff_2 diff_3 diff_4 u3_0 u3_1 u3_2 u3_3 u3_4 tmp_0 tmp_1 tmp_2 tmp_3 tmp_4 a24e_0 a24e_1 a24e_2 a24e_3 a24e_4 u2_0 u2_1 u2_2 u2_3 u2_4 a24epbb_0 a24epbb_1 a24epbb_2 a24epbb_3 a24epbb_4 w2_0 w2_1 w2_2 w2_3 w2_4 w3_0 w3_1 w3_2 w3_3 w3_4 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12) (hsp : s.sp = S)
    (hr0 : s.regs.regs 0#5 = Pb) (hr1 : s.regs.regs 1#5 = Qb) (hr2 : s.regs.regs 2#5 = u1)
    (hs : s.mem ⊨ ((S - 96#64) ↦₆₄* [sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 832#64) ↦₆₄* [g0]) ∗ ((S - 824#64) ↦₆₄* [a_0, a_1, a_2, a_3, a_4]) ∗ ((S - 784#64) ↦₆₄* [b_0, b_1, b_2, b_3, b_4]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = mpl.base 12 + BitVec.ofNat 64 192 ∧
      sf.sp = S - 832#64 ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ t144 t164 t76 t96 t100 t120 t68 t188 t172 t176 t180 t156 t168 t160 t72 t84 t80 t104 t112 t136 t108 t132 t124 t140 t148 t152 : BitVec 64,
        sf.regs.regs 0#5 = t120 ∧
        sf.regs.regs 1#5 = t68 ∧
        sf.regs.regs 2#5 = u1 ∧
        sf.regs.regs 8#5 = t188 ∧
        sf.regs.regs 9#5 = t172 ∧
        sf.regs.regs 10#5 = t176 ∧
        sf.regs.regs 11#5 = t180 ∧
        sf.regs.regs 12#5 = t144 ∧
        sf.regs.regs 13#5 = t156 ∧
        sf.regs.regs 14#5 = t168 ∧
        sf.regs.regs 15#5 = t160 ∧
        sf.regs.regs 16#5 = t100 ∧
        sf.regs.regs 17#5 = p8 ∧
        sf.regs.regs 18#5 = p9 ∧
        sf.regs.regs 19#5 = Qb ∧
        sf.regs.regs 20#5 = Pb ∧
        sf.regs.regs 21#5 = (s.regs.regs 21#5) ∧
        sf.regs.regs 22#5 = 0x007ffffffffffff0#64 ∧
        sf.regs.regs 23#5 = (s.regs.regs 23#5) ∧
        sf.regs.regs 24#5 = 36028797018963664#64 ∧
        sf.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64) ∧
        sf.regs.regs 26#5 = (s.regs.regs 26#5) ∧
        sf.regs.regs 27#5 = (s.regs.regs 27#5) ∧
        sf.regs.regs 28#5 = (s.regs.regs 28#5) ∧
        sf.regs.regs 29#5 = (S - 96#64) ∧
        sf.regs.regs 30#5 = (s.regs.regs 30#5) ∧
        (t68 = p9 + p4) ∧
        (t72 = p4 - p9) ∧
        (t76 = p5 + p0) ∧
        (t80 = p0 + 36028797018963664#64) ∧
        (t84 = t72 + 0x007ffffffffffff0#64) ∧
        (t96 = p6 + p1) ∧
        (t100 = p7 + p2) ∧
        (t104 = p1 - p6) ∧
        (t108 = t84 >>> 51) ∧
        (t112 = t80 - p5) ∧
        (t120 = p8 + p3) ∧
        (t124 = t104 + 0x007ffffffffffff0#64) ∧
        (t132 = p2 - p7) ∧
        (t136 = t112 &&& 0x0007ffffffffffff#64) ∧
        (t140 = p3 - p8) ∧
        (t144 = t136 + (t108.setWidth 32).setWidth 64 * (((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64).setWidth 32).setWidth 64) ∧
        (t148 = t132 + 0x007ffffffffffff0#64) ∧
        (t152 = t124 &&& 0x0007ffffffffffff#64) ∧
        (t156 = t140 + 0x007ffffffffffff0#64) ∧
        (t160 = t148 &&& 0x0007ffffffffffff#64) ∧
        (t164 = t152 + t112 >>> 51) ∧
        (t168 = t156 &&& 0x0007ffffffffffff#64) ∧
        (t172 = t160 + t124 >>> 51) ∧
        (t176 = t84 &&& 0x0007ffffffffffff#64) ∧
        (t180 = t168 + t148 >>> 51) ∧
        (t188 = t176 + t156 >>> 51) ∧
        sf.mem ⊨ ((S - 784#64) ↦₆₄* [t144, t164, b_2, b_3, b_4]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, a_3, a_4]) ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [(s.regs.regs 29#5), (s.regs.regs 30#5), (s.regs.regs 28#5), (s.regs.regs 27#5), (s.regs.regs 26#5), (s.regs.regs 25#5), (s.regs.regs 24#5), (s.regs.regs 23#5), (s.regs.regs 22#5), (s.regs.regs 21#5), (s.regs.regs 20#5), (s.regs.regs 19#5)]) ∗ ((S - 744#64) ↦₆₄* [c_0, c_1, c_2, c_3, c_4]) ∗ ((S - 704#64) ↦₆₄* [d_0, d_1, d_2, d_3, d_4]) ∗ ((S - 664#64) ↦₆₄* [aa_0, aa_1, aa_2, aa_3, aa_4]) ∗ ((S - 624#64) ↦₆₄* [bb_0, bb_1, bb_2, bb_3, bb_4]) ∗ ((S - 584#64) ↦₆₄* [e_0, e_1, e_2, e_3, e_4]) ∗ ((S - 544#64) ↦₆₄* [da_0, da_1, da_2, da_3, da_4]) ∗ ((S - 504#64) ↦₆₄* [cb_0, cb_1, cb_2, cb_3, cb_4]) ∗ ((S - 464#64) ↦₆₄* [sum_0, sum_1, sum_2, sum_3, sum_4]) ∗ ((S - 424#64) ↦₆₄* [diff_0, diff_1, diff_2, diff_3, diff_4]) ∗ ((S - 384#64) ↦₆₄* [u3_0, u3_1, u3_2, u3_3, u3_4]) ∗ ((S - 344#64) ↦₆₄* [tmp_0, tmp_1, tmp_2, tmp_3, tmp_4]) ∗ ((S - 304#64) ↦₆₄* [a24e_0, a24e_1, a24e_2, a24e_3, a24e_4]) ∗ ((S - 264#64) ↦₆₄* [u2_0, u2_1, u2_2, u2_3, u2_4]) ∗ ((S - 224#64) ↦₆₄* [a24epbb_0, a24epbb_1, a24epbb_2, a24epbb_3, a24epbb_4]) ∗ ((S - 184#64) ↦₆₄* [w2_0, w2_1, w2_2, w2_3, w2_4]) ∗ ((S - 144#64) ↦₆₄* [w3_0, w3_1, w3_2, w3_3, w3_4]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  sorry

end X25519Dalek
