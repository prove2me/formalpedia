-- Prove2me | Theorems.Thm_ZlibCrc32_subroutineOk_crc32_combine_and_crc32_combine64
-- name    : ZlibCrc32.subroutineOk_crc32_combine_and_crc32_combine64
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T01:32:49.339575+00:00
-- url     : https://prove2.me/theorems/f3bd63d5-4870-435e-8bcc-aa4713673933
-- title:
--   zlib.h, crc32_combine() — crc32_combine and crc32_combine64 combine two CRC-32s
-- statement:
--   Total correctness of both `crc32_combine` and `crc32_combine64` in the AArch64 object code of zlib 1.3.1's `crc32.c`, with the same contract for each. "Total correctness" is read as in the goal: for every placement of the library, frame and AAPCS64 entry state, the function terminates and returns with the calling convention preserved.
--
--   `crc1` is in `x0`, `crc2` in `x1` and `len2` in `x2`, a signed 64-bit integer; the result is in `x0`. Let $A$ and $B$ be byte strings with:
--   - the low 32 bits of `crc1` the CRC-32 of $A$, that is, with polynomial $\mathrm{CRC}_u(M_A, 0)$;
--   - the low 32 bits of `crc2` the CRC-32 of $B$;
--   - `len2` $= |B|$ (in particular non-negative).
--
--   Then the result is a 32-bit value (upper half zero) whose polynomial is $\mathrm{CRC}_u(M_{AB}, 0)$, the CRC-32 of $A$ followed by $B$. The caller lends the library's tables and gets them back; no other memory is used.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), zlib.h lines 1754–1762 (crc32_combine) and 1864 (crc32_combine64)

import Mathlib
import Definitions.Def_ZlibCrc32_Spec

namespace ZlibCrc32

theorem subroutineOk_crc32_combine_and_crc32_combine64 :
    zlibCrc32Lib.subroutineOk "crc32_combine" crc32CombineSpec ∧
      zlibCrc32Lib.subroutineOk "crc32_combine64" crc32CombineSpec := by
  sorry

end ZlibCrc32
