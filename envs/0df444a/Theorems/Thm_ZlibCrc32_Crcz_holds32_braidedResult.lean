-- Prove2me | Theorems.Thm_ZlibCrc32_Crcz_holds32_braidedResult
-- name    : ZlibCrc32.Crcz.holds32_braidedResult
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T13:14:07.041808+00:00
-- url     : https://prove2.me/theorems/a891624b-59a1-4927-8118-aa80e3146d3d
-- title:
--   The braided computation (N = 5, W = 8) computes CRC-32 — braidedResult crc bs q K is crc32Poly crc bs
-- statement:
--   For every 32-bit value `crc`, byte list `bs` and natural numbers $q, K$ with $q + 40(K+1) \le |bs|$, the zero-extension to 64 bits of `braidedResult crc bs q K` satisfies `Holds32` for `crc32Poly crc bs`. That value is what zlib's braided `crc32_z` (N = 5 braids of W = 8-byte words) returns: the first $q$ bytes byte-wise from $\lnot$`crc`, then $K$ blocks of 40 bytes on five braids with `crc_braid_table`, the last block $K$ folded word by word with `crc_word`, the remaining bytes byte-wise, and the result complemented. The tables are the library's `crc_table` and `crc_braid_table` as placed in the object.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32.c lines 694–1013 (braided crc32_z, N = 5, W = 8)

import Definitions.Def_ZlibCrc32_CrczModel

namespace ZlibCrc32.Crcz

theorem holds32_braidedResult (crc : BitVec 32) (bs : List (BitVec 8)) (q K : ℕ)
    (h : q + 40 * (K + 1) ≤ bs.length) :
    Holds32 ((braidedResult crc bs q K).setWidth 64) (crc32Poly crc bs) := by
  sorry

end ZlibCrc32.Crcz
