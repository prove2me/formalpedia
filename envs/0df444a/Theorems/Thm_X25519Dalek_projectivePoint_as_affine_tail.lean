-- Prove2me | Theorems.Thm_X25519Dalek_projectivePoint_as_affine_tail
-- name    : X25519Dalek.projectivePoint_as_affine_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T14:45:59.459162+00:00
-- url     : https://prove2.me/theorems/7d0a684e-ff26-4db8-99be-6c176c355f0e
-- title:
--   The last 98 instructions of the compiled ProjectivePoint::as_affine (to_bytes and epilogue) meet their contract
-- statement:
--   A segment contract for block 11 of `x25519CliMultiLib` (`<curve25519_dalek::montgomery::ProjectivePoint>::as_affine`), offsets 128 to 516: the inlined `FieldElement51::to_bytes` of the field element $u$ just computed, followed by the function epilogue.
--
--   For every placement `mpl` of the library that is placeable, and every machine state $s$ in which the library's code is loaded, that is running, whose program counter is the block's base plus 128 and whose stack pointer is $S - 272$ (16-byte aligned), with `x19` $=$ `out` and `x29` $= S - 48$, and whose memory satisfies
--
--   $$(S-128) \mapsto u \;\ast\; \mathtt{out} \mapsto b \;\ast\; (S-48) \mapsto_{64} [v_{29}, v_{30}, v_{28}, v_{21}, v_{20}, v_{19}] \;\ast\; F$$
--
--   where $u$ is a 40-byte `FieldElement51` with five limbs below $2^{52}$, $b$ is any 32 bytes and $F$ is any frame: execution of the block's program reaches a state that equals $s$ except for the program counter, the general registers, the stack pointer, the flags and the memory, with program counter $v_{30}$ (the return), stack pointer $S$, registers `x19`, `x20`, `x21`, `x28`, `x29` restored to $v_{19}, v_{20}, v_{21}, v_{28}, v_{29}$, registers `x22`–`x27` unchanged, and memory satisfying the same assertion with $b$ replaced by $\mathrm{natToLeBytes}_{32}(\mathrm{fe51ValOfBytes}(u) \bmod p)$, the canonical encoding of $u$. The vector registers are unchanged because the final state is $s$ with only the listed fields replaced.
--
--   It is an intermediate step for `X25519Dalek.fnOk_projectivePoint_as_affine`, splitting that proof in two; the segment and its contract follow DeepMind's proof of the block (`projective_point_as_affine_ok_of`, google-deepmind/code-verification @ 8c8d371f, `Shared51/MontgomeryLadderCode1.lean`).
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/MontgomeryLadderCode1.lean, theorem projective_point_as_affine_ok_of, https://github.com/google-deepmind/code-verification

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem projectivePoint_as_affine_tail {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S out : BitVec 64} {uaff out_bs : List (BitVec 8)}
    {v29 v30 v28 v21 v20 v19 : BitVec 64} {F : Arm64.SepProp}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 11 + 128#64) (hsp : s.sp = S - 272#64)
    (hal : (S - 272#64 &&& 15#64) = 0#64) (h19 : s.regs.regs 19#5 = out)
    (h29 : s.regs.regs 29#5 = S - 48#64) (hub : fe51LimbsBounded uaff (2 ^ 52)) (hlo : out_bs.length = 32)
    (hs : s.mem ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ out_bs) ∗
      ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F) :
    ∃ (rf : BitVec 5 → BitVec 64) (ps : Arm64.PState) (m' : Arm64.Memory),
      Arm64.Steps (x25519CliMultiLib.blockProgram mpl 11) s
        { s with pc := v30, regs := ⟨rf⟩, sp := S, pstate := ps, mem := m' } ∧
      rf 19#5 = v19 ∧ rf 20#5 = v20 ∧ rf 21#5 = v21 ∧ rf 28#5 = v28 ∧ rf 29#5 = v29 ∧
      rf 22#5 = s.regs.regs 22#5 ∧ rf 23#5 = s.regs.regs 23#5 ∧ rf 24#5 = s.regs.regs 24#5 ∧
      rf 25#5 = s.regs.regs 25#5 ∧ rf 26#5 = s.regs.regs 26#5 ∧ rf 27#5 = s.regs.regs 27#5 ∧
      m' ⊨ ((S - 128#64) ↦ₛ uaff) ∗ (out ↦ₛ natToLeBytes 32 (fe51ValOfBytes uaff % p25519)) ∗
        ((S - 48#64) ↦₆₄* [v29, v30, v28, v21, v20, v19]) ∗ F := by
  sorry

end X25519Dalek
