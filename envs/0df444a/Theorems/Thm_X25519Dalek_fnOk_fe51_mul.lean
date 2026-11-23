-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_fe51_mul
-- name    : X25519Dalek.fnOk_fe51_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T21:25:23.400148+00:00
-- url     : https://prove2.me/theorems/66c2f16b-e2c0-41d9-89e2-6474e26fc241
-- title:
--   &FieldElement51 * &FieldElement51 — the compiled multiplication mod 2^255 − 19, in three calling modes
-- statement:
--   Total correctness of `<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`), under three contracts at once. For each, for every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The common precondition: `x8` holds the address `out` of a 40-byte result buffer, `x0` and `x1` the addresses of two `FieldElement51`s $a$ and $b$ with every limb below $2^{54}$, in buffers disjoint from each other and from `out`. The caller owns `out` and the 224 bytes below the stack pointer. The postcondition: `out` holds a `FieldElement51` with every limb below $2^{52}$ whose value is congruent mod $p$ to the product of the values of $a$ and $b$; $a$, $b$ and the stack frame are handed back. The three contracts differ only in the permission on the operands:
--   - `fe51MulSpec`: both $a$ and $b$ owned (writable);
--   - `fe51MulRoRightSpec`: $a$ owned, $b$ read-only;
--   - `fe51MulRoLeftSpec`: $a$ read-only, $b$ owned.
--
--   curve25519-dalek 5.0.0, src/backend/serial/u64/field.rs, lines 111–115: the function has no documentation comment; it is “impl<'a> Mul<&'a FieldElement51> for &FieldElement51 { type Output = FieldElement51; [...] fn mul(self, _rhs: &'a FieldElement51) -> FieldElement51 {”. Lines 30–32: “In the 64-bit implementation, a `FieldElement` is represented in radix $2^{51}$ as five `u64`s; the coefficients are allowed to grow up to $2^{54}$ between reductions modulo $p$.”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/backend/serial/u64/field.rs, lines 111–115 (Mul for &FieldElement51)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_fe51_mul :
    fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulSpec) ∧
      fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulRoRightSpec) ∧
      fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulRoLeftSpec) := by
  sorry

end X25519Dalek
