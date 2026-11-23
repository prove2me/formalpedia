-- Prove2me | Theorems.Thm_X25519Dalek_basepointTable_mul_base_odd_iter
-- name    : X25519Dalek.basepointTable_mul_base_odd_iter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T20:19:41.831147+00:00
-- url     : https://prove2.me/theorems/44efc67e-5dc0-4438-8126-80609ba55509
-- title:
--   EdwardsBasepointTable::mul_base on AArch64, one odd-digit iteration
-- statement:
--   For every placement `mpl` under which the library is placeable, every iteration index $i < 32$ and every state $s$ in which the library's code is loaded, running at `mpl.base 13 + 152` with stack pointer $S$ (16-byte aligned), `x20` = `table`, `x21` = $S+232$, `x22` = $S$, `x24` = $S+392$, `x23` = $2i$, `x25` = 960 and `x29` = $S+672$, and whose memory satisfies, with an arbitrary frame $F$: the read-only table bytes `table_bs` at `table` (every limb of its 32 sub-tables below $2^{53}$), 64 owned digit bytes at $S$, an accumulator `acc_bs` at $S+64$ (a 160-byte point with limbs below $2^{52}$), owned scratch buffers of 160, 160 and 120 bytes at $S+232$, $S+392$, $S+552$, and the 912-byte region below $S$: block 13's program runs from $s$ to a running state $s'$ with stack pointer $S$, `pc` at `mpl.base 13 + 316` if $i = 31$ and back at `mpl.base 13 + 152` otherwise, `x23` = $2(i+1)$, the other callee-saved registers `x19`–`x29` and the callee-saved vector registers unchanged, and memory satisfying the same assertion with new buffer contents of the same lengths and a new accumulator `acc'` whose limbs are below $2^{52}$ and with `edExtOfBytes acc' = edMulBaseStep table_bs i d (edExtOfBytes acc_bs)`, where $d$ is digit number $2i+1$ (the odd digits are processed by this loop).
--
--   In the source this is one iteration of the odd-digit loop of `mul_base`: select the multiple of the basepoint for digit $d$ from sub-table $i$ (`LookupTable::select`), add it to the accumulator (`EdwardsPoint + AffineNielsPoint`), and convert the result back to an extended point (four multiplications).
--
--   This is a named step of the machine-code proof of `EdwardsBasepointTable::mul_base` (block 13 of the x25519-dalek mission's placed object `x25519CliMultiLib`), published so that the proof fits the verifier's CPU limit in several pieces. Its route is DeepMind's proof of `mul_base` (google-deepmind/code-verification @ 8c8d371f, `Shared51/BasepointTable.lean`). Notation: $S$ is the stack pointer after the prologue; the frame below the saved registers holds the 64 radix-16 digits at $S$, the accumulator point (160 bytes) at $S+64$, scratch points at $S+232$ (extended), $S+392$ (completed) and $S+552$ (an `AffineNielsPoint`, 120 bytes), and the callees use the 912 bytes below $S$.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/BasepointTable.lean (edwards_basepoint_table_mul_base_ok_of, mul_base_odd_loop, mul_base_even_loop), https://github.com/google-deepmind/code-verification

import Mathlib.ModelTheory.Semantics
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem basepointTable_mul_base_odd_iter {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S table : BitVec 64} {i : Nat}
    {table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8)} {F : Arm64.SepProp}
    (hi : i < 32) (hrun : s.status = .Running) (hpc : s.pc = mpl.base 13 + 152#64) (hsp : s.sp = S)
    (hal : (S &&& 15#64) = 0#64)
    (h20 : s.regs.regs 20#5 = table)
    (h21 : s.regs.regs 21#5 = S + 232#64)
    (h22 : s.regs.regs 22#5 = S)
    (h23 : s.regs.regs 23#5 = BitVec.ofNat 64 (2 * i))
    (h24 : s.regs.regs 24#5 = S + 392#64)
    (h25 : s.regs.regs 25#5 = 960#64)
    (h29 : s.regs.regs 29#5 = S + 672#64)
    (htab : fe51BasepointTable32Bounded table_bs (2 ^ 53)) (hdig : digits.length = 64)
    (hacc : fe51Point4Bounded acc_bs (2 ^ 52)) (hext : ext_bs.length = 160)
    (hcomp : comp_bs.length = 160) (hniels : niels_bs.length = 120)
    (hs : s.mem ⊨ (table ↦ᵣ table_bs) ∗ (S ↦ₛ digits) ∗ ((S + 64#64) ↦ₛ acc_bs) ∗
      ((S + 232#64) ↦ₛ ext_bs) ∗ ((S + 392#64) ↦ₛ comp_bs) ∗ ((S + 552#64) ↦ₛ niels_bs) ∗
      Arm64.memRegion (S - 912#64) 912 ∗ F) :
    ∃ s' : Arm64.State, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 13) s s' ∧
      s'.status = .Running ∧
      s'.pc = (if i = 31 then mpl.base 13 + 316#64 else mpl.base 13 + 152#64) ∧ s'.sp = S ∧
      s'.regs.regs 23#5 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      (∀ k : BitVec 5, k ≠ 23#5 → 19 ≤ k.toNat → k.toNat < 30 → s'.regs.regs k = s.regs.regs k) ∧
      Arm64.VRegFile.calleeSaved s'.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ acc' ext' comp' niels' : List (BitVec 8),
        (s'.mem ⊨ (table ↦ᵣ table_bs) ∗ (S ↦ₛ digits) ∗ ((S + 64#64) ↦ₛ acc') ∗
          ((S + 232#64) ↦ₛ ext') ∗ ((S + 392#64) ↦ₛ comp') ∗ ((S + 552#64) ↦ₛ niels') ∗
          Arm64.memRegion (S - 912#64) 912 ∗ F) ∧
        fe51Point4Bounded acc' (2 ^ 52) ∧
        edExtOfBytes acc' = edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) (edExtOfBytes acc_bs) ∧
        ext'.length = 160 ∧ comp'.length = 160 ∧ niels'.length = 120 := by
  sorry

end X25519Dalek
