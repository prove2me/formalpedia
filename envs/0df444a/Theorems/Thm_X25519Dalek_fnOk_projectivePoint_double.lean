-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_projectivePoint_double
-- name    : X25519Dalek.fnOk_projectivePoint_double
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T21:43:00.044154+00:00
-- url     : https://prove2.me/theorems/6845c2a8-16ca-4f60-a23c-0262b1c01cd8
-- title:
--   ProjectivePoint::double — the compiled Edwards doubling
-- statement:
--   Total correctness of `<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`projectivePointDoubleSpec`): `x8` holds the address `out` of a 160-byte result buffer and `x0` the address of a 120-byte projective point $(X : Y : Z)$ with limbs below $2^{53}, 2^{53}, 2^{54}$. The caller owns both buffers and the 400 bytes below the stack pointer. The postcondition: `out` holds a 160-byte `CompletedPoint` with limbs below $2^{52}, 2^{53}, 2^{52}, 2^{52}$ whose coordinates mod $p$ are `edProjDouble X Y Z`: with $XX = X^2$, $YY = Y^2$, $ZZ2 = 2Z^2$, $(X+Y)^2$, the result is $((X+Y)^2 - (XX + YY),\ XX + YY,\ YY - XX,\ ZZ2 - (YY - XX))$ mod $p$. The input and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/backend/serial/curve_models.rs, line 380: “Double this point: return self + self”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/backend/serial/curve_models.rs, lines 380–381 (ProjectivePoint::double)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_projectivePoint_double :
    fnOk
      "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double"
      (fun _ => projectivePointDoubleSpec) := by
  sorry

end X25519Dalek
