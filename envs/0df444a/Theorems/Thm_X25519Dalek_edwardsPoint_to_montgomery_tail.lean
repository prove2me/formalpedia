-- Prove2me | Theorems.Thm_X25519Dalek_edwardsPoint_to_montgomery_tail
-- name    : X25519Dalek.edwardsPoint_to_montgomery_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T18:13:47.511845+00:00
-- url     : https://prove2.me/theorems/7282c017-bc1d-4b78-a5b5-4c28328c9dff
-- title:
--   EdwardsPoint::to_montgomery, final segment (to_bytes and return) on AArch64
-- statement:
--   A named step of the machine-code proof of `EdwardsPoint::to_montgomery` (block 10 of the x25519-dalek mission's placed object, `x25519CliMultiLib`), published so that the proof fits the verifier's resource limits in two pieces. For every placement `mpl` under which the library is placeable, every state $s$ in which the library's code is loaded, running, at `mpl.base 10 + 296` with stack pointer $S - 352$ (16-byte aligned), `x19` holding the output address `out`, `x20` holding 19 and `x29` holding $S - 48$, and whose memory satisfies, with an arbitrary frame $F$: 40 owned bytes `uaff` at $S - 128$ (a `FieldElement51` with all five limbs $< 2^{52}$), 32 owned bytes at `out`, and the six saved 64-bit words $v_{29}, v_{30}, v_{28}, v_{21}, v_{20}, v_{19}$ at $S - 48$: block 10's program runs from $s$ to a state equal to $s$ except that `pc` $= v_{30}$, `sp` $= S$, flags, memory and general registers are new, the registers `x19`, `x20`, `x21`, `x28`, `x29` hold $v_{19}, v_{20}, v_{21}, v_{28}, v_{29}$, the registers `x22`–`x27` are unchanged, and the new memory satisfies the same assertion with `out` now holding `natToLeBytes 32 (fe51ValOfBytes uaff % p25519)`, the canonical 32-byte little-endian encoding of the field element.
--
--   This is the `FieldElement51::to_bytes` computation inlined at the end of `to_montgomery` followed by the epilogue (restore the callee-saved registers and return). It is the same form as the mission's step `X25519Dalek.projectivePoint_as_affine_tail` for block 11, whose code it repeats shifted by 164 bytes, except that block 10 already holds 19 in `x20` (hypothesis `h20`). The route is DeepMind's proof of `EdwardsPoint::to_montgomery` (google-deepmind/code-verification @ 8c8d371f, `Shared51/ToMontgomery.lean`).
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/ToMontgomery.lean (the to_bytes tail of edwards_point_to_montgomery_ok), https://github.com/google-deepmind/code-verification

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem edwardsPoint_to_montgomery_tail {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S out : BitVec 64} {uaff out_bs : List (BitVec 8)}
    {v29 v30 v28 v21 v20 v19 : BitVec 64} {F : Arm64.SepProp}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 10 + 296#64) (hsp : s.sp = S - 352#64)
    (hal : (S - 352#64 &&& 15#64) = 0#64) (h19 : s.regs.regs 19#5 = out) (h20 : s.regs.regs 20#5 = 19#64)
    (h29 : s.regs.regs 29#5 = S - 48#64) (hub : fe51LimbsBounded uaff (2 ^ 52)) (hlo : out_bs.length = 32)
    (hs : s.mem ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ out_bs) ∗
      ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F) :
    ∃ (rf : BitVec 5 → BitVec 64) (ps : Arm64.PState) (m' : Arm64.Memory),
      Arm64.Steps (x25519CliMultiLib.blockProgram mpl 10) s
        { s with pc := v30, regs := ⟨rf⟩, sp := S, pstate := ps, mem := m' } ∧
      rf 19#5 = v19 ∧ rf 20#5 = v20 ∧ rf 21#5 = v21 ∧ rf 28#5 = v28 ∧ rf 29#5 = v29 ∧
      rf 22#5 = s.regs.regs 22#5 ∧ rf 23#5 = s.regs.regs 23#5 ∧ rf 24#5 = s.regs.regs 24#5 ∧
      rf 25#5 = s.regs.regs 25#5 ∧ rf 26#5 = s.regs.regs 26#5 ∧ rf 27#5 = s.regs.regs 27#5 ∧
      m' ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ natToLeBytes 32 (fe51ValOfBytes uaff % p25519)) ∗
        ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F := by
  sorry

end X25519Dalek
