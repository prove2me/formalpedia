-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_basepointTable_mul_base
-- name    : X25519Dalek.fnOk_basepointTable_mul_base
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T22:06:56.292837+00:00
-- url     : https://prove2.me/theorems/2bc0ee50-85ca-49b5-a14d-abf8220542ab
-- title:
--   EdwardsBasepointTable::mul_base — the compiled radix-16 fixed-base multiplication
-- statement:
--   Total correctness of `<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`edwardsBasepointTableMulBaseSpec`): `x8` holds the address `out` of a 160-byte result buffer, `x0` the address of a table of 30,720 read-only bytes in which each of the 32 sub-tables of 960 bytes has all its limbs below $2^{53}$ (`fe51BasepointTable32Bounded`), and `x1` the address of 32 scalar bytes $s$ whose last byte is at most $127$. The caller also owns the read-only constant `FieldElement51::ONE` and the 1,680 bytes below the stack pointer. The postcondition: `out` holds an `EdwardsPoint` with every limb below $2^{52}$ whose coordinates mod $p$ are `edMulBase` of the table bytes and $s$; the table, $s$, the constant and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/traits.rs, lines 61–62: “Multiply a `scalar` by this precomputed basepoint table, in constant time.”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/traits.rs, lines 61–62 (BasepointTable::mul_base), implemented in src/edwards.rs, lines 1150–1192

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_basepointTable_mul_base :
    fnOk
      "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base"
      edwardsBasepointTableMulBaseSpec := by
  sorry

end X25519Dalek
