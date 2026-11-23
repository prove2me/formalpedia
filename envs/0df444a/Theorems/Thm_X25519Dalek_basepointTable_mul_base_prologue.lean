-- Prove2me | Theorems.Thm_X25519Dalek_basepointTable_mul_base_prologue
-- name    : X25519Dalek.basepointTable_mul_base_prologue
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T20:19:40.474062+00:00
-- url     : https://prove2.me/theorems/9bb1104f-9a06-453b-9514-1aafa03b4b1b
-- title:
--   EdwardsBasepointTable::mul_base on AArch64, prologue and radix-16 recoding
-- statement:
--   For every placement `mpl` under which the library is placeable and every state $s$ in which the library's code is loaded, running at `mpl.base 13` (the entry of `mul_base`) with stack pointer $S + 768$ ($S$ 16-byte aligned), `x0` = `table`, `x1` = `scalar`, `x8` = `out`, and whose memory satisfies, with an arbitrary frame $G$: owned regions of 96, 160 and 64 bytes at $S+672$, $S+64$ and $S$, the 32 owned scalar bytes `scalar_bs` at `scalar` (top byte at most 127), and the read-only bytes of `FieldElement51::ONE`: block 13's program runs from $s$ to a running state $s'$ at `mpl.base 13 + 152` (the head of the odd-digit loop) with stack pointer $S$, `x19` = `out`, `x20` = `table`, `x21` = $S+232$, `x22` = $S$, `x23` = 0, `x24` = $S+392$, `x25` = 960, `x29` = $S+672$, `x26`–`x28` and the callee-saved vector registers unchanged, and memory in which the twelve saved registers (`x29`, `x30`, `x28`, an unspecified word, `x26`, ..., `x19` of $s$) are stored at $S+672$, the accumulator at $S+64$ is a 160-byte point with limbs below $2^{52}$ equal to the identity (`edExtOfBytes acc = edExtZero`), the digits `scalarRadix16Digits scalar_bs` are at $S$, and the scalar, `ONE` and $G$ are unchanged.
--
--   In the source this is the prologue of `mul_base`, the call `Scalar::as_radix_16` and the initialisation of the accumulator to the identity point.
--
--   This is a named step of the machine-code proof of `EdwardsBasepointTable::mul_base` (block 13 of the x25519-dalek mission's placed object `x25519CliMultiLib`), published so that the proof fits the verifier's CPU limit in several pieces. Its route is DeepMind's proof of `mul_base` (google-deepmind/code-verification @ 8c8d371f, `Shared51/BasepointTable.lean`). Notation: $S$ is the stack pointer after the prologue; the frame below the saved registers holds the 64 radix-16 digits at $S$, the accumulator point (160 bytes) at $S+64$, scratch points at $S+232$ (extended), $S+392$ (completed) and $S+552$ (an `AffineNielsPoint`, 120 bytes), and the callees use the 912 bytes below $S$.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/BasepointTable.lean (edwards_basepoint_table_mul_base_ok_of, mul_base_odd_loop, mul_base_even_loop), https://github.com/google-deepmind/code-verification

import Mathlib.Computability.Reduce
import Mathlib.ModelTheory.Semantics
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem basepointTable_mul_base_prologue {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S table scalar out : BitVec 64}
    {scalar_bs : List (BitVec 8)} {G : Arm64.SepProp}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 13) (hsp : s.sp = S + 768#64)
    (hal : (S &&& 15#64) = 0#64)
    (h0 : s.regs.regs 0#5 = table) (h1 : s.regs.regs 1#5 = scalar) (h8 : s.regs.regs 8#5 = out)
    (hsc : scalar_bs.length = 32) (hsc31 : (scalar_bs.getD 31 0#8).toNat ≤ 127)
    (hs : s.mem ⊨ Arm64.memRegion (S + 672#64) 96 ∗ Arm64.memRegion (S + 64#64) 160 ∗ Arm64.memRegion S 64 ∗
      (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) :
    ∃ s' : Arm64.State, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 13) s s' ∧
      s'.status = .Running ∧ s'.pc = mpl.base 13 + 152#64 ∧ s'.sp = S ∧
      s'.regs.regs 19#5 = out ∧ s'.regs.regs 20#5 = table ∧ s'.regs.regs 21#5 = S + 232#64 ∧
      s'.regs.regs 22#5 = S ∧ s'.regs.regs 23#5 = 0#64 ∧ s'.regs.regs 24#5 = S + 392#64 ∧
      s'.regs.regs 25#5 = 960#64 ∧ s'.regs.regs 26#5 = s.regs.regs 26#5 ∧
      s'.regs.regs 27#5 = s.regs.regs 27#5 ∧ s'.regs.regs 28#5 = s.regs.regs 28#5 ∧
      s'.regs.regs 29#5 = S + 672#64 ∧
      Arm64.VRegFile.calleeSaved s'.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ (w3 : BitVec 64) (acc : List (BitVec 8)),
        (s'.mem ⊨ ((S + 672#64) ↦₆₄* [s.regs.regs 29#5, s.regs.regs 30#5, s.regs.regs 28#5, w3, s.regs.regs 26#5, s.regs.regs 25#5, s.regs.regs 24#5, s.regs.regs 23#5, s.regs.regs 22#5, s.regs.regs 21#5, s.regs.regs 20#5, s.regs.regs 19#5]) ∗ ((S + 64#64) ↦ₛ acc) ∗
          (S ↦ₛ scalarRadix16Digits scalar_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) ∧
        fe51Point4Bounded acc (2 ^ 52) ∧ edExtOfBytes acc = edExtZero := by
  sorry

end X25519Dalek
