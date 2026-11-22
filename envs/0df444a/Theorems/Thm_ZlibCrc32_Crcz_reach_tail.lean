-- Prove2me | Theorems.Thm_ZlibCrc32_Crcz_reach_tail
-- name    : ZlibCrc32.Crcz.reach_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T13:14:05.398907+00:00
-- url     : https://prove2.me/theorems/16dc1eb3-e577-4718-b9a8-50c089c47bbb
-- title:
--   crc32_z's byte tail (offset 0x714) processes the last 1–7 bytes and returns ~crcBytes
-- statement:
--   For a run of `crc32_z` with environment `Env pl s0 bs m` (see the bundle), suppose the abstract state at library offset 1824 (function offset 0x714) has the stack pointer `spIn s0`, `x1` = buffer $+ p$, `x2` $= r$ with $1 \le r \le 7$ and $p + r = |bs|$, `x9` the zero-extension of a 32-bit $c$, and `x13` the placed address of `crc_table` (other registers and flags arbitrary). Then `Reach`: the program returns to the caller of `s0` with `x0` the zero-extension of $\lnot$`crcBytes c` of the bytes of `bs` from position $p$, the callee-saved registers and stack pointer restored, and `FrameOk s0` for the final memory.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32_z's byte tail, AArch64 object code at function offset 0x714

import Definitions.Def_ZlibCrc32_CrczModel

open Arm64 Arm64.Obj

namespace ZlibCrc32.Crcz

theorem reach_tail {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory}
    {ps : PState} {R : Regs} (hE : Env pl s0 bs m) (c : BitVec 32) (p r : ℕ)
    (hpr : p + r = bs.length) (hr1 : 1 ≤ r) (hr7 : r ≤ 7)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 p) (h2 : R.x2 = BitVec.ofNat 64 r)
    (h9 : R.x9 = c.setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym) :
    Reach pl s0 ((~~~ crcBytes c (bs.drop p)).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 1824#64) ps R) := by
  sorry

end ZlibCrc32.Crcz
