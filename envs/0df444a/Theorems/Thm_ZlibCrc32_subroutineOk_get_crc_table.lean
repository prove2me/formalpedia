-- Prove2me | Theorems.Thm_ZlibCrc32_subroutineOk_get_crc_table
-- name    : ZlibCrc32.subroutineOk_get_crc_table
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T01:35:30.478182+00:00
-- url     : https://prove2.me/theorems/5cbe27e6-729a-4bee-a49d-14e400d9d6d2
-- title:
--   zlib.h, get_crc_table() — get_crc_table returns the byte-wise CRC table
-- statement:
--   Total correctness of `get_crc_table` in the AArch64 object code of zlib 1.3.1's `crc32.c`. "Total correctness" is read as in the goal: for every placement of the library, frame and AAPCS64 entry state, the function terminates and returns with the calling convention preserved.
--
--   The caller lends the library's tables and gets them back. The result `x0` is the address of the library's `crc_table` under the placement, and points to 1024 readable bytes holding 256 little-endian 32-bit words. Word $i$ is the polynomial of byte $i$ times $x^{32}$, mod the CRC-32 polynomial $P$, which is $\mathrm{CRC}_0$ of the one-byte message $i$ from the initial value $0$ (Kadatch–Jenkins eq. (7)).
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), zlib.h line 1916 and crc32.c lines 546–554 (get_crc_table)

import Mathlib
import Definitions.Def_ZlibCrc32_Spec

namespace ZlibCrc32

theorem subroutineOk_get_crc_table :
    zlibCrc32Lib.subroutineOk "get_crc_table" getCrcTableSpec := by
  sorry

end ZlibCrc32
