-- Prove2me | Theorems.Thm_X25519Dalek_differentialAddAndDouble_828_ret
-- name    : X25519Dalek.differentialAddAndDouble_828_ret
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:33:11.522542+00:00
-- url     : https://prove2.me/theorems/6ad42e8c-7af0-4b43-80d3-4a0854cc0d36
-- title:
--   The compiled curve25519-dalek differential_add_and_double, offsets 828–948: the copies to the outputs and the epilogue, meets its segment contract
-- statement:
--   A segment contract for block 12 of `x25519CliMultiLib` (`curve25519_dalek::montgomery::differential_add_and_double`), offsets 828–948: the copies to the outputs and the epilogue. For every placeable placement `mpl` and every running state `s` with the library's code loaded, whose program counter, stack pointer, registers and memory are as in the hypotheses (the 1,056-byte stack frame below the entry stack pointer `S` split into 64-bit word lists, the projective points `P` and `Q` and the base point `u1` as word lists whose limbs are below the stated bounds, the constant `121666` read-only, and any frame `F`), execution of the block's program reaches a state `sf` that is running, at the stated program counter and stack pointer, with the callee-saved vector registers unchanged, and, for some 64-bit words, with the stated register contents, memory and facts.
--
--   It copies U2, W2 to the 80 bytes at P and U3, W3 to the 80 bytes at Q with 128- and 64-bit loads and stores, releases the frame, reloads the callee-saved registers and returns. The stack frame is again one 1,056-byte region. Limb bounds are stated as `w.toNat < 2^k` for each limb and values as `fe51Val w0 w1 w2 w3 w4 % p25519`, with the field operations `fpAdd`, `fpSub`, `fpPow` of the mission's definitions.
--
--   This is one of ten consecutive segments into which the proof of `X25519Dalek.fnOk_differential_add_and_double` is split so that each part fits the verifier's limits; the segments, their formulas and the contract follow DeepMind's proof of the block (`differential_add_and_double_ok_of` and `diff_add_mid`, google-deepmind/code-verification @ 8c8d371f, `Shared51/MontgomeryLadderCode1.lean`).
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/MontgomeryLadderCode1.lean, theorems differential_add_and_double_ok_of and diff_add_mid, https://github.com/google-deepmind/code-verification

import Mathlib
import Definitions.Def_X25519Dalek_Spec

set_option maxHeartbeats 4000000

namespace X25519Dalek

theorem differentialAddAndDouble_828_ret {mpl : Arm64.Obj.MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S Pb Qb u1 : BitVec 64} {F : Arm64.SepProp}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {o166 o167 o168 o169 o170 o235 o236 o237 o238 o239 t452 t476 t488 t492 t484 t768 t772 t784 t788 t792 o220 o221 o222 o223 o224 o181 o182 o183 o184 o185 o64 o65 o66 o67 o68 o79 o80 o81 o82 o83 o196 o197 o198 o199 o200 t632 t644 t660 t676 t680 t560 t564 t584 t588 t616 o151 o152 o153 o154 o155 o118 o119 o120 o121 o122 o103 o104 o105 o106 o107 t144 t164 t172 t180 t188 t232 t228 t248 t256 t276 t76 t96 t100 t120 t68 t316 t328 t324 t336 t348 g1 : BitVec 64}
    (hal : (S &&& 15#64 == 0#64) = true)
    (hPU : p0.toNat < 9007199254740992 ∧ p1.toNat < 9007199254740992 ∧ p2.toNat < 9007199254740992 ∧ p3.toNat < 9007199254740992 ∧ p4.toNat < 9007199254740992)
    (hPW : p5.toNat < 9007199254740992 ∧ p6.toNat < 9007199254740992 ∧ p7.toNat < 9007199254740992 ∧ p8.toNat < 9007199254740992 ∧ p9.toNat < 9007199254740992)
    (hQU : q0.toNat < 9007199254740992 ∧ q1.toNat < 9007199254740992 ∧ q2.toNat < 9007199254740992 ∧ q3.toNat < 9007199254740992 ∧ q4.toNat < 9007199254740992)
    (hQW : q5.toNat < 9007199254740992 ∧ q6.toNat < 9007199254740992 ∧ q7.toNat < 9007199254740992 ∧ q8.toNat < 9007199254740992 ∧ q9.toNat < 9007199254740992)
    (hU1 : uw0.toNat < 18014398509481984 ∧ uw1.toNat < 18014398509481984 ∧ uw2.toNat < 18014398509481984 ∧ uw3.toNat < 18014398509481984 ∧ uw4.toNat < 18014398509481984)
    (hrun : s.status = Arm64.ExecStatus.Running) (hpc : s.pc = mpl.base 12 + BitVec.ofNat 64 828) (hsp : s.sp = S - 832#64)
    (hr19 : s.regs.regs 19#5 = Qb)
    (hr20 : s.regs.regs 20#5 = Pb)
    (hr21 : s.regs.regs 21#5 = o80)
    (hr22 : s.regs.regs 22#5 = 0x007ffffffffffff0#64)
    (hr23 : s.regs.regs 23#5 = o79)
    (hr24 : s.regs.regs 24#5 = 36028797018963664#64)
    (hr25 : s.regs.regs 25#5 = ((((19#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64))
    (hr26 : s.regs.regs 26#5 = o83)
    (hr27 : s.regs.regs 27#5 = o82)
    (hr28 : s.regs.regs 28#5 = o81)
    (hr29 : s.regs.regs 29#5 = (S - 96#64))
    (bd_Tmp : (o166.toNat < 4503599627370496 ∧ o167.toNat < 4503599627370496 ∧ o168.toNat < 4503599627370496 ∧ o169.toNat < 4503599627370496 ∧ o170.toNat < 4503599627370496))
    (bd_W3 : (o235.toNat < 4503599627370496 ∧ o236.toNat < 4503599627370496 ∧ o237.toNat < 4503599627370496 ∧ o238.toNat < 4503599627370496 ∧ o239.toNat < 4503599627370496))
    (bd_E : (t452.toNat < 4503599627370496 ∧ t476.toNat < 4503599627370496 ∧ t488.toNat < 4503599627370496 ∧ t492.toNat < 4503599627370496 ∧ t484.toNat < 4503599627370496))
    (bd_A24EpBB : (t768.toNat < 9007199254740992 ∧ t772.toNat < 9007199254740992 ∧ t784.toNat < 9007199254740992 ∧ t788.toNat < 9007199254740992 ∧ t792.toNat < 9007199254740992))
    (bd_W2 : (o220.toNat < 4503599627370496 ∧ o221.toNat < 4503599627370496 ∧ o222.toNat < 4503599627370496 ∧ o223.toNat < 4503599627370496 ∧ o224.toNat < 4503599627370496))
    (bd_A24E : (o181.toNat < 4503599627370496 ∧ o182.toNat < 4503599627370496 ∧ o183.toNat < 4503599627370496 ∧ o184.toNat < 4503599627370496 ∧ o185.toNat < 4503599627370496))
    (bd_AA : (o64.toNat < 4503599627370496 ∧ o65.toNat < 4503599627370496 ∧ o66.toNat < 4503599627370496 ∧ o67.toNat < 4503599627370496 ∧ o68.toNat < 4503599627370496))
    (bd_BB : (o79.toNat < 4503599627370496 ∧ o80.toNat < 4503599627370496 ∧ o81.toNat < 4503599627370496 ∧ o82.toNat < 4503599627370496 ∧ o83.toNat < 4503599627370496))
    (bd_U2 : (o196.toNat < 4503599627370496 ∧ o197.toNat < 4503599627370496 ∧ o198.toNat < 4503599627370496 ∧ o199.toNat < 4503599627370496 ∧ o200.toNat < 4503599627370496))
    (bd_Diff : (t632.toNat < 4503599627370496 ∧ t644.toNat < 4503599627370496 ∧ t660.toNat < 4503599627370496 ∧ t676.toNat < 4503599627370496 ∧ t680.toNat < 4503599627370496))
    (bd_Sum : (t560.toNat < 9007199254740992 ∧ t564.toNat < 9007199254740992 ∧ t584.toNat < 9007199254740992 ∧ t588.toNat < 9007199254740992 ∧ t616.toNat < 9007199254740992))
    (bd_U3 : (o151.toNat < 4503599627370496 ∧ o152.toNat < 4503599627370496 ∧ o153.toNat < 4503599627370496 ∧ o154.toNat < 4503599627370496 ∧ o155.toNat < 4503599627370496))
    (bd_CB : (o118.toNat < 4503599627370496 ∧ o119.toNat < 4503599627370496 ∧ o120.toNat < 4503599627370496 ∧ o121.toNat < 4503599627370496 ∧ o122.toNat < 4503599627370496))
    (bd_DA : (o103.toNat < 4503599627370496 ∧ o104.toNat < 4503599627370496 ∧ o105.toNat < 4503599627370496 ∧ o106.toNat < 4503599627370496 ∧ o107.toNat < 4503599627370496))
    (bd_B : (t144.toNat < 4503599627370496 ∧ t164.toNat < 4503599627370496 ∧ t172.toNat < 4503599627370496 ∧ t180.toNat < 4503599627370496 ∧ t188.toNat < 4503599627370496))
    (bd_C : (t232.toNat < 18014398509481984 ∧ t228.toNat < 18014398509481984 ∧ t248.toNat < 18014398509481984 ∧ t256.toNat < 18014398509481984 ∧ t276.toNat < 18014398509481984))
    (bd_A : (t76.toNat < 18014398509481984 ∧ t96.toNat < 18014398509481984 ∧ t100.toNat < 18014398509481984 ∧ t120.toNat < 18014398509481984 ∧ t68.toNat < 18014398509481984))
    (bd_D : (t316.toNat < 4503599627370496 ∧ t328.toNat < 4503599627370496 ∧ t324.toNat < 4503599627370496 ∧ t336.toNat < 4503599627370496 ∧ t348.toNat < 4503599627370496))
    (hs : s.mem ⊨ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 344#64) ↦₆₄* [o166, o167, o168, o169, o170]) ∗ ((S - 144#64) ↦₆₄* [o235, o236, o237, o238, o239]) ∗ Arm64.memRegion (S - 832#64 - 224#64) 224 ∗ ((S - 832#64) ↦₆₄* [u1]) ∗ ((S - 584#64) ↦₆₄* [t452, t476, t488, t492, t484]) ∗ ((S - 224#64) ↦₆₄* [t768, t772, t784, t788, t792]) ∗ ((S - 184#64) ↦₆₄* [o220, o221, o222, o223, o224]) ∗ ((S - 304#64) ↦₆₄* [o181, o182, o183, o184, o185]) ∗ ((S - 664#64) ↦₆₄* [o64, o65, o66, o67, o68]) ∗ ((S - 624#64) ↦₆₄* [o79, o80, o81, o82, o83]) ∗ ((S - 264#64) ↦₆₄* [o196, o197, o198, o199, o200]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ ((S - 424#64) ↦₆₄* [t632, t644, t660, t676, t680]) ∗ ((S - 464#64) ↦₆₄* [t560, t564, t584, t588, t616]) ∗ ((S - 384#64) ↦₆₄* [o151, o152, o153, o154, o155]) ∗ ((S - 504#64) ↦₆₄* [o118, o119, o120, o121, o122]) ∗ ((S - 544#64) ↦₆₄* [o103, o104, o105, o106, o107]) ∗ ((S - 784#64) ↦₆₄* [t144, t164, t172, t180, t188]) ∗ ((S - 744#64) ↦₆₄* [t232, t228, t248, t256, t276]) ∗ ((S - 824#64) ↦₆₄* [t76, t96, t100, t120, t68]) ∗ ((S - 704#64) ↦₆₄* [t316, t328, t324, t336, t348]) ∗ (Qb ↦₆₄* [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]) ∗ (Pb ↦₆₄* [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 104#64) ↦₆₄* [g1]) ∗ F) :
    ∃ sf, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 12) s sf ∧
      sf.status = Arm64.ExecStatus.Running ∧
      sf.pc = c30 ∧
      sf.sp = S ∧
      Arm64.VRegFile.calleeSaved sf.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      sf.regs.regs 19#5 = c19 ∧
        sf.regs.regs 20#5 = c20 ∧
        sf.regs.regs 21#5 = c21 ∧
        sf.regs.regs 22#5 = c22 ∧
        sf.regs.regs 23#5 = c23 ∧
        sf.regs.regs 24#5 = c24 ∧
        sf.regs.regs 25#5 = c25 ∧
        sf.regs.regs 26#5 = c26 ∧
        sf.regs.regs 27#5 = c27 ∧
        sf.regs.regs 28#5 = c28 ∧
        sf.regs.regs 29#5 = c29 ∧
        sf.mem ⊨ Arm64.memRegion (S - 1056#64) 1056 ∗ (Qb ↦₆₄* [o151, o152, o153, o154, o155, o235, o236, o237, o238, o239]) ∗ (Pb ↦₆₄* [o196, o197, o198, o199, o200, o220, o221, o222, o223, o224]) ∗ (u1 ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((fe51_mont_a24 mpl) ↦ᵣ fe51MontA24Bytes) ∗ F := by
  sorry

end X25519Dalek
