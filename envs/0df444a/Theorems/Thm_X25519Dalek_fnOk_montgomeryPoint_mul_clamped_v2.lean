-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_montgomeryPoint_mul_clamped_v2
-- name    : X25519Dalek.fnOk_montgomeryPoint_mul_clamped_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:16:12.895575+00:00
-- url     : https://prove2.me/theorems/caf1cdfc-60ec-4c9c-8504-dc3e414a3edd
-- title:
--   MontgomeryPoint::mul_clamped — the compiled code computes X25519(bytes, self)
-- statement:
--   Total correctness of `<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`: the function need not be exported). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`montgomeryPointMulClampedSpec`): `x8` holds the address `out` of a 32-byte result buffer, `x0` the address of the 32 bytes $u$ of `self`, and `x1` the address of 32 bytes $k$. The caller owns the three buffers, the read-only constants `FieldElement51::ONE` and $121666$, and the 1,728 bytes below the stack pointer. The postcondition: `out` holds $\mathrm{X25519}(k, u)$ (`x25519 k u`, bundle `X25519Dalek_Rfc7748`), the buffer of $k$ now holds the clamped bytes (`clampScalarBytes k`), and $u$, the constants and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/montgomery.rs, lines 148–149: “Multiply this point by `clamp_integer(bytes)`. For a description of clamping, see [`clamp_integer`].”
--
--   **Replaces** `X25519Dalek.fnOk_montgomeryPoint_mul_clamped`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/montgomery.rs, lines 148–150 (MontgomeryPoint::mul_clamped)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_montgomeryPoint_mul_clamped_v2 :
    fnOk
      "<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped"
      montgomeryPointMulClampedSpec := by
  sorry

end X25519Dalek
