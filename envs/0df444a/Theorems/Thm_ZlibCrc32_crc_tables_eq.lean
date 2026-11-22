-- Prove2me | Theorems.Thm_ZlibCrc32_crc_tables_eq
-- name    : ZlibCrc32.crc_tables_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T01:35:55.364201+00:00
-- url     : https://prove2.me/theorems/d649906b-f220-4006-ba31-7026dc63f346
-- title:
--   crc32.c, the CRC tables — crc_table, crc_braid_table and x2n_table hold their CRC values
-- statement:
--   The three data objects of the compiled library, read as little-endian 32-bit words, hold the following values. $P$ is the CRC-32 polynomial, and the polynomial of a word is read by the register convention: bit $i$ is the coefficient of $x^{31-i}$.
--   - `crc_table` is 1024 bytes. Its word $i$ ($i < 256$) is $\mathrm{CRC}_0$ of the one-byte message $i$ from $0$, that is $B_i(x)\,x^{32} \bmod P$. Here $B_i(x)$ is the polynomial of byte $i$: bit $j$ of $i$ is the coefficient of $x^{7-j}$.
--   - `crc_braid_table` is 8192 bytes. Its word $256k + i$ ($k < 8$, $i < 256$) is $B_i(x)\,x^{8(5 \cdot 8 + 3 - k)} \bmod P$.
--   - `x2n_table` is 128 bytes. Its word $k$ ($k < 32$) is $\mathrm{Pow2k}(k) = x^{2^k} \bmod P$ (Kadatch–Jenkins eq. (6)).
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32.c lines 142–143 (the CRC tables)

import Mathlib
import Definitions.Def_ZlibCrc32_Spec

open Polynomial KadatchJenkins

namespace ZlibCrc32

theorem crc_tables_eq :
    (zlibCrc32PlacedData0.length = 1024 ∧ ∀ i < 256,
      regPoly (word32 zlibCrc32PlacedData0 i) = crc0 crc32P (Message.ofBytes [BitVec.ofNat 8 i]) 0) ∧
    (zlibCrc32PlacedData1.length = 8192 ∧ ∀ k < 8, ∀ i < 256,
      regPoly (word32 zlibCrc32PlacedData1 (256 * k + i)) =
        (Message.ofBytes [BitVec.ofNat 8 i]).poly * X ^ (8 * (5 * 8 + 3 - k)) % crc32P) ∧
    (zlibCrc32PlacedData2.length = 128 ∧ ∀ k < 32,
      regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k) := by
  sorry

end ZlibCrc32
