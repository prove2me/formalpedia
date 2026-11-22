-- Prove2me | Theorems.Thm_ZlibCrc32_Crcz_holds32_crcBytes
-- name    : ZlibCrc32.Crcz.holds32_crcBytes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T13:13:57.132516+00:00
-- url     : https://prove2.me/theorems/8d7dc145-60e3-48f5-bdb1-081248e7bb57
-- title:
--   The byte-wise table loop computes CRC-32 — ~crcBytes(~crc, bs) is crc32Poly crc bs
-- statement:
--   For every 32-bit value `crc` and byte list `bs`, the zero-extension to 64 bits of $\lnot\,$`crcBytes (~crc) bs` — zlib's byte-wise loop `crc = crc_table[(crc ^ b) & 0xff] ^ (crc >> 8)` over `bs`, with pre- and post-conditioning — satisfies `Holds32` for `crc32Poly crc bs`: its upper 32 bits are zero and the polynomial of its low 32 bits (Kadatch–Jenkins register convention) is the CRC-32 $\mathrm{CRC}_u(M, v)$ of the message $M$ of `bs` continued from the polynomial $v$ of `crc`. The table is the library's `crc_table` as placed in the object.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32.c lines 990–1006 and 704, 1009 (byte-wise loop with pre- and post-conditioning)

import Definitions.Def_ZlibCrc32_CrczModel

namespace ZlibCrc32.Crcz

theorem holds32_crcBytes (crc : BitVec 32) (bs : List (BitVec 8)) :
    Holds32 ((~~~ crcBytes (~~~ crc) bs).setWidth 64) (crc32Poly crc bs) := by
  sorry

end ZlibCrc32.Crcz
