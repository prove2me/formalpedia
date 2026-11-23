-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_to_montgomery_v2
-- name    : X25519Dalek.fnOk_edwardsPoint_to_montgomery_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:17.304597+00:00
-- url     : https://prove2.me/theorems/917b5e01-e2c2-4a3b-8240-442a30b631ef
-- title:
--   EdwardsPoint::to_montgomery — the compiled map u = (Z + Y)/(Z − Y)
-- statement:
--   Total correctness of `<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`edwardsPointToMontgomerySpec`): `x8` holds the address `out` of a 32-byte result buffer and `x0` the address of a 160-byte `EdwardsPoint` $(X, Y, Z, T)$ with every limb below $2^{53}$ (`fe51Point4Bounded`). The caller owns both buffers and the 1,392 bytes below the stack pointer. The postcondition: `out` holds the 32 little-endian bytes of $(Z + Y)(Z - Y)^{p-2} \bmod p$ (`edExtToMontgomeryU`), with $Y, Z$ the coordinates mod $p$; the point and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/edwards.rs, lines 571–576: “Convert this `EdwardsPoint` on the Edwards model to the corresponding `MontgomeryPoint` on the Montgomery model. This function has one exceptional case; the identity point of the Edwards curve is sent to the 2-torsion point $(0,0)$ on the Montgomery curve.”
--
--   **Replaces** `X25519Dalek.fnOk_edwardsPoint_to_montgomery`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/edwards.rs, lines 571–580 (to_montgomery)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_edwardsPoint_to_montgomery_v2 :
    fnOk
      "<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery"
      (fun _ => edwardsPointToMontgomerySpec) := by
  sorry

end X25519Dalek
