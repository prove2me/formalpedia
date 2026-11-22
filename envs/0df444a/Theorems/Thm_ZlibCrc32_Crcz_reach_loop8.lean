-- Prove2me | Theorems.Thm_ZlibCrc32_Crcz_reach_loop8
-- name    : ZlibCrc32.Crcz.reach_loop8
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T13:14:07.303154+00:00
-- url     : https://prove2.me/theorems/482281fe-a730-4f5d-b50f-787e5d760020
-- title:
--   crc32_z's 8-bytes-per-iteration loop (offset 0x658) and what follows return ~crcBytes of the rest
-- statement:
--   For a run of `crc32_z` with environment `Env pl s0 bs m` (see the bundle), suppose the abstract state at library offset 1636 (function offset 0x658) has the stack pointer `spIn s0`, `x1` = buffer $+ p$ with $p + 8 \le |bs|$, `x2` $= |bs| - p$, `x9` the zero-extension of a 32-bit $c$, and `x13` the placed address of `crc_table` (other registers and flags arbitrary). Then `Reach`: the program returns to the caller of `s0` with `x0` the zero-extension of $\lnot$`crcBytes c` of the bytes of `bs` from position $p$, the callee-saved registers and stack pointer restored, and `FrameOk s0` for the final memory. The loop handles 8 bytes per iteration while at least 8 remain, then the byte tail or the return.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32_z's 8-byte loop, AArch64 object code at function offset 0x658

import Definitions.Def_ZlibCrc32_CrczModel

open Arm64 Arm64.Obj

namespace ZlibCrc32.Crcz

theorem reach_loop8 {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory}
    {ps : PState} {R : Regs} (hE : Env pl s0 bs m) (c : BitVec 32) (p : ℕ)
    (hp : p + 8 ≤ bs.length)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 p)
    (h2 : R.x2 = BitVec.ofNat 64 (bs.length - p))
    (h9 : R.x9 = c.setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym) :
    Reach pl s0 ((~~~ crcBytes c (bs.drop p)).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 1636#64) ps R) := by
  sorry

end ZlibCrc32.Crcz
