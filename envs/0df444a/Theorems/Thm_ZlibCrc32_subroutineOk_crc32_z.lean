-- Prove2me | Theorems.Thm_ZlibCrc32_subroutineOk_crc32_z
-- name    : ZlibCrc32.subroutineOk_crc32_z
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T01:36:38.114248+00:00
-- url     : https://prove2.me/theorems/e51f88de-94f4-45b2-a395-51736439474d
-- title:
--   zlib.h, crc32_z() — the compiled crc32_z computes CRC-32
-- statement:
--   Total correctness of `crc32_z` in the AArch64 object code of zlib 1.3.1's `crc32.c` (`zlibCrc32Lib`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the address of `crc32_z` with the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates. It returns to the caller (the link register) with the stack pointer and the callee-saved registers restored, $R$ untouched, and the postcondition holding. It never panics, exits or runs out of memory.
--
--   The arguments follow AAPCS64: `crc` in `x0`, `buf` in `x1`, `len` in `x2`, the result in `x0`. In every case the caller lends the 96 bytes below the stack pointer (any contents) and the library's three tables in their initial state, and gets both back.
--   - **`buf = Z_NULL`** (`x1 = 0`), any `crc` and `len`: the result is $0$.
--   - **`buf ≠ Z_NULL`**, with the bytes $b_0, \dots, b_{n-1}$ readable at `buf` and `len` $= n$: the result is a 32-bit value (upper half of `x0` zero) whose polynomial is $\mathrm{CRC}_u(M, v)$. Here $M$ is the message of $b_0 \dots b_{n-1}$ (bit $i$ of byte $j$ is message bit $8j + i$), $v$ is the polynomial of the low 32 bits of `crc`, $P$ is the CRC-32 polynomial and $u = x^{31} + \dots + x + 1$. The buffer is handed back unchanged.
--
--   Polynomials of 32-bit values are Kadatch–Jenkins' register convention: bit $i$ is the coefficient of $x^{31-i}$.
--
--   zlib.h, lines 1732–1736 and 1751: “Update a running CRC-32 with the bytes buf[0..len-1] and return the updated CRC-32. A CRC-32 value is in the range of a 32-bit unsigned integer. If buf is Z_NULL, this function returns the required initial value for the crc. Pre- and post-conditioning (one's complement) is performed within this function so it shouldn't be done by the application.” (of `crc32`), and of `crc32_z`: “Same as crc32(), but with a size_t length.”
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), zlib.h lines 1730–1752 (crc32, crc32_z)

import Mathlib
import Definitions.Def_ZlibCrc32_Spec

namespace ZlibCrc32

theorem subroutineOk_crc32_z : zlibCrc32Lib.subroutineOk "crc32_z" crc32zSpec := by
  sorry

end ZlibCrc32
