-- Prove2me | Theorems.Thm_ZlibCrc32_subroutineOk_crc32
-- name    : ZlibCrc32.subroutineOk_crc32
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T01:31:49.995139+00:00
-- url     : https://prove2.me/theorems/8eb2a5d9-bd7f-4f1f-b692-afd8e7f97b5a
-- title:
--   zlib.h, crc32() — the compiled crc32 computes CRC-32
-- statement:
--   Total correctness of `crc32` in the AArch64 object code of zlib 1.3.1's `crc32.c` (`zlibCrc32Lib`), with the same reading of total correctness as the goal. It holds for every placement of the library, frame and AAPCS64 entry state, and the function terminates and returns with the calling convention preserved.
--
--   `crc` is in `x0`, `buf` in `x1` and `len` in `x2`, and the result is in `x0`. `len` is a 32-bit `uInt`, so its value is the low 32 bits of `x2`. The caller lends the 96 bytes below the stack pointer (any contents) and the library's three tables, and gets both back.
--   - **`buf = Z_NULL`** (`x1 = 0`): the result is $0$.
--   - **`buf ≠ Z_NULL`**, with the bytes $b_0, \dots, b_{n-1}$ readable at `buf` and the low 32 bits of `x2` equal to $n$: the result is a 32-bit value (upper half of `x0` zero) whose polynomial is $\mathrm{CRC}_u(M, v)$. $M$ is the message of the bytes, $v$ the polynomial of the low 32 bits of `crc`, $P$ the CRC-32 polynomial and $u = x^{31} + \dots + 1$. The buffer is handed back unchanged.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), zlib.h lines 1730–1745 (crc32)

import Mathlib
import Definitions.Def_ZlibCrc32_Spec

namespace ZlibCrc32

theorem subroutineOk_crc32 : zlibCrc32Lib.subroutineOk "crc32" crc32Spec := by
  sorry

end ZlibCrc32
