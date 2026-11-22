-- Prove2me | Theorems.Thm_ZlibCrc32Bytewise_subroutineOk_crc32_z
-- name    : ZlibCrc32Bytewise.subroutineOk_crc32_z
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T01:53:50.913258+00:00
-- url     : https://prove2.me/theorems/b904e1b1-0bc9-46ff-8a20-99f80accc8c4
-- title:
--   zlib 1.3.1 crc32_z, byte-at-a-time build on AArch64, computes zlib's table loop
-- statement:
--   Total correctness of `crc32_z` in the AArch64 object code of zlib 1.3.1's `crc32.c` built with `-DZ_TESTW=` (`zlibCrc32Lib`, bundle `ZlibCrc32Bytewise_PlacedObj`), under the contract `crc32zSpec` (bundle `ZlibCrc32Bytewise_Spec`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$, and every entry state at the address of `crc32_z` with the stack pointer 16-byte aligned whose memory holds the placed code and satisfies the precondition separately from $R$, execution reaches a state where it has returned: to the caller (the link register), with the stack pointer and the callee-saved registers restored, $R$ untouched, and the postcondition holding. It never panics, exits or runs out of memory.
--
--   The precondition: `x1` (`buf`) is non-zero, `x2` (`len`) equals the number $n$ of bytes $b_0, \dots, b_{n-1}$ readable at `buf`, and the library's data objects (among them `crc_table`) are in their initial state. The postcondition: `x0` is the zero-extension to 64 bits of `crcModel` with the library's `crc_table` bytes, that is, with $c$ the low 32 bits of the entry `x0`, the value $\lnot\,s_n$ where $s_0 = \lnot c$ and $s_{j+1} = (s_j \gg 8) \oplus T[(s_j \oplus b_j) \bmod 256]$, $T[i]$ the little-endian word at bytes $4i, \dots, 4i+3$ of `crc_table`. The buffer and the data objects are handed back unchanged.
--
--   This is crc32.c's code path for `crc32_z` when `W` is undefined (lines 694–1010 without lines 706–989): the pre-conditioning `crc = (~crc) & 0xffffffff` (line 704), the loop `crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]` (lines 990–1006), and `return crc ^ 0xffffffff` (line 1009). The statement is about the machine code, not the C source; it does not assert that `crc_table` holds the CRC-32 table, and it does not cover `buf = Z_NULL`. zlib's default build, with the braided loop, is the mission "zlib 1.3.1 CRC-32 on AArch64", whose goal `ZlibCrc32.subroutineOk_crc32_z` states the result as the CRC-32 polynomial.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32_z (crc32.c lines 694–1010) in the -DZ_TESTW= build, where W is undefined and lines 706–989 are not compiled

import Definitions.Def_ZlibCrc32Bytewise_Spec

namespace ZlibCrc32Bytewise

theorem subroutineOk_crc32_z : zlibCrc32Lib.subroutineOk "crc32_z" crc32zSpec := by
  sorry

end ZlibCrc32Bytewise
