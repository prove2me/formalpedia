-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_fe51_mul_v2
-- name    : X25519Dalek.fnOk_fe51_mul_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:18.148281+00:00
-- url     : https://prove2.me/theorems/44137a83-f3b2-47f1-9ab2-13ae6db47609
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
--
--   **Replaces** `X25519Dalek.fnOk_fe51_mul`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/backend/serial/u64/field.rs, lines 111–115 (Mul for &FieldElement51)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_fe51_mul_v2 :
    fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulSpec) ∧
      fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulRoRightSpec) ∧
      fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulRoLeftSpec) := by
  sorry

end X25519Dalek
