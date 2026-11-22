-- Prove2me | Theorems.Thm_ZlibCrc32_subroutineOk_crc32_combine_gen_and_crc32_combine_gen64
-- name    : ZlibCrc32.subroutineOk_crc32_combine_gen_and_crc32_combine_gen64
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T01:33:45.260168+00:00
-- url     : https://prove2.me/theorems/6ad766c4-4850-43c3-8dc1-3f1d39a6fc70
-- title:
--   zlib.h, crc32_combine_gen() — crc32_combine_gen and crc32_combine_gen64 return x^(8·len2) mod P
-- statement:
--   Total correctness of both `crc32_combine_gen` and `crc32_combine_gen64` in the AArch64 object code of zlib 1.3.1's `crc32.c`, with the same contract for each. "Total correctness" is read as in the goal: for every placement of the library, frame and AAPCS64 entry state, the function terminates and returns with the calling convention preserved.
--
--   `len2` is in `x0`, a signed 64-bit integer, and the result is in `x0`. If `len2` $= n \ge 0$, the result is a 32-bit value (upper half zero) whose polynomial is $x^{8n} \bmod P$, where $P$ is the CRC-32 polynomial. The caller lends the library's tables and gets them back.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), zlib.h lines 1764–1769 (crc32_combine_gen) and 1865 (crc32_combine_gen64)

import Mathlib
import Definitions.Def_ZlibCrc32_Spec

namespace ZlibCrc32

theorem subroutineOk_crc32_combine_gen_and_crc32_combine_gen64 :
    zlibCrc32Lib.subroutineOk "crc32_combine_gen" crc32CombineGenSpec ∧
      zlibCrc32Lib.subroutineOk "crc32_combine_gen64" crc32CombineGenSpec := by
  sorry

end ZlibCrc32
