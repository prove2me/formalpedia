-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_to_montgomery
-- name    : X25519Dalek.fnOk_edwardsPoint_to_montgomery
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T22:17:52.727804+00:00
-- url     : https://prove2.me/theorems/202c5c0d-e458-4506-b295-9ebc19b4701b
-- title:
--   EdwardsPoint::to_montgomery — the compiled map u = (Z + Y)/(Z − Y)
-- statement:
--   Total correctness of `<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`edwardsPointToMontgomerySpec`): `x8` holds the address `out` of a 32-byte result buffer and `x0` the address of a 160-byte `EdwardsPoint` $(X, Y, Z, T)$ with every limb below $2^{53}$ (`fe51Point4Bounded`). The caller owns both buffers and the 1,392 bytes below the stack pointer. The postcondition: `out` holds the 32 little-endian bytes of $(Z + Y)(Z - Y)^{p-2} \bmod p$ (`edExtToMontgomeryU`), with $Y, Z$ the coordinates mod $p$; the point and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/edwards.rs, lines 571–576: “Convert this `EdwardsPoint` on the Edwards model to the corresponding `MontgomeryPoint` on the Montgomery model. This function has one exceptional case; the identity point of the Edwards curve is sent to the 2-torsion point $(0,0)$ on the Montgomery curve.”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/edwards.rs, lines 571–580 (to_montgomery)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_edwardsPoint_to_montgomery :
    fnOk
      "<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery"
      (fun _ => edwardsPointToMontgomerySpec) := by
  sorry

end X25519Dalek
