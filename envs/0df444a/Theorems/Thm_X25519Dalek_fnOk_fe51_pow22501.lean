-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_fe51_pow22501
-- name    : X25519Dalek.fnOk_fe51_pow22501
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T21:34:17.38391+00:00
-- url     : https://prove2.me/theorems/1560d6a0-2aad-4570-8626-f54e84aae8a7
-- title:
--   FieldElement::pow22501 — the compiled (x^(2^250 − 1), x^11)
-- statement:
--   Total correctness of `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`fe51Pow22501Spec`): `x0` holds the address `out` of an 80-byte result buffer and `x1` the address of a 40-byte `FieldElement51` $x$ with every limb below $2^{54}$. The caller owns both buffers and the 1,040 bytes below the stack pointer. The postcondition: `out` holds two `FieldElement51`s, every limb below $2^{52}$, whose values mod $p$ are $x^{2^{250} - 1}$ and $x^{11}$ (`fpPow`), with $x$ the value of the input mod $p$. The input and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/field.rs, lines 173–174: “Compute (self^(2^250-1), self^11), used as a helper function within invert() and pow22523().”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/field.rs, lines 173–176 (pow22501)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_fe51_pow22501 :
    fnOk
      "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501"
      (fun _ => fe51Pow22501Spec) := by
  sorry

end X25519Dalek
