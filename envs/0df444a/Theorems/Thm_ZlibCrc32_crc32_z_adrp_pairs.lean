-- Prove2me | Theorems.Thm_ZlibCrc32_crc32_z_adrp_pairs
-- name    : ZlibCrc32.crc32_z_adrp_pairs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T13:14:20.052269+00:00
-- url     : https://prove2.me/theorems/07e49a04-58d5-46ed-a098-98a9f893f34f
-- title:
--   crc32_z's three ADRP/ADD table-address pairs decode, for any placement, as address computations of their table
-- statement:
--   For every placement `pl` of `zlibCrc32Lib` that the linker could produce (`Placeable`) and every memory `m` in which the placed program (no hooks) is loaded, consider the instruction words at library offsets $o = 28$, $456$ and $1040$ (with destination register $x13$, $x12$, $x13$ and symbol `crc_table`, `crc_braid_table`, `crc_table` respectively), with $P$ = base $+ o$ and $T$ the placed address of the symbol. Either the words at $P$ and $P + 4$ decode to `adrp` (page-relative address) writing $\mathrm{page}(T) - \mathrm{page}(P)$ offset into the register and `add` of the low 12 bits of $T$ to it (64-bit, register to itself), or (the linker's relaxation) to `nop` and `adr` writing the offset $T - (P + 4)$ into the register. These are the relocated `adrp`/`add` pairs by which `crc32_z` loads the addresses of `crc_table` and `crc_braid_table`.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32_z's relocated adrp/add pairs for crc_table and crc_braid_table (AArch64 object code)

import Definitions.Def_ZlibCrc32_PlacedObj

open Arm64 Arm64.Obj

namespace ZlibCrc32

theorem crc32_z_adrp_pairs (pl : Placement) (hP : zlibCrc32Lib.Placeable pl) (m : Memory)
    (hCL : (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).CodeLoaded m)
    (o : Nat) (rd : BitVec 5) (sym : String)
    (h : (o = 28 ∧ rd = 13#5 ∧ sym = "crc_table [zlib_crc32]") ∨
      (o = 456 ∧ rd = 12#5 ∧ sym = "crc_braid_table [zlib_crc32]") ∨
      (o = 1040 ∧ rd = 13#5 ∧ sym = "crc_table [zlib_crc32]")) :
    ((zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 o) =
        some (.adr true (.gpr rd) (pageOf (pl.ρ sym) - pageOf (pl.base + BitVec.ofNat 64 o))) ∧
      (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 (o + 4)) =
        some (.addSubImm .W64 .ADD (.gpr rd) (.gpr rd) ((pl.ρ sym).extractLsb' 0 12) false)) ∨
    ((zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 o) = some .nop ∧
      (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 (o + 4)) =
        some (.adr false (.gpr rd) (pl.ρ sym - (pl.base + BitVec.ofNat 64 (o + 4))))) := by
  sorry

end ZlibCrc32
