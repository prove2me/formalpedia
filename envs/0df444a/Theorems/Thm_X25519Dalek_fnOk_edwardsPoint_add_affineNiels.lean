-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_add_affineNiels
-- name    : X25519Dalek.fnOk_edwardsPoint_add_affineNiels
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T21:43:28.050951+00:00
-- url     : https://prove2.me/theorems/85d4e72c-205a-4efa-8692-461bcc886f31
-- title:
--   EdwardsPoint + AffineNielsPoint — the compiled mixed addition
-- statement:
--   Total correctness of `<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`edwardsPointAddAffineNielsSpec`): `x8` holds the address `out` of a 160-byte result buffer, `x0` the address of a 160-byte `EdwardsPoint` $(X, Y, Z, T)$ with limbs below $2^{53}, 2^{53}, 2^{52}, 2^{54}$ in the four coordinates, and `x1` the address of a 120-byte `AffineNielsPoint` $(y{+}x,\ y{-}x,\ xy2d)$ with limbs below $2^{54}$. The caller owns the three buffers and the 528 bytes below the stack pointer. The postcondition: `out` holds a 160-byte `CompletedPoint` with limbs below $2^{52}, 2^{53}, 2^{54}, 2^{52}$ whose coordinates mod $p$ are `edAddAffineNiels`: with $PP = (Y + X)(y{+}x)$, $MM = (Y - X)(y{-}x)$, $TT2d = T \cdot xy2d$ and $ZZ2 = 2Z$, the result is $(PP - MM,\ PP + MM,\ ZZ2 + TT2d,\ ZZ2 - TT2d)$ mod $p$. The inputs and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/backend/serial/curve_models.rs, lines 455–458: the function has no documentation comment; its signature is “impl<'a> Add<&'a AffineNielsPoint> for &EdwardsPoint { type Output = CompletedPoint; fn add(self, other: &'a AffineNielsPoint) -> CompletedPoint {”.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/backend/serial/curve_models.rs, lines 455–458 (Add<&AffineNielsPoint> for &EdwardsPoint)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_edwardsPoint_add_affineNiels :
    fnOk
      "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add"
      (fun _ => edwardsPointAddAffineNielsSpec) := by
  sorry

end X25519Dalek
