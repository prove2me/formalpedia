-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_projectivePoint_as_affine_v2
-- name    : X25519Dalek.fnOk_projectivePoint_as_affine_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:21.54922+00:00
-- url     : https://prove2.me/theorems/9c30b6a6-f882-472b-a097-937565476299
-- title:
--   montgomery::ProjectivePoint::as_affine — the compiled u = U/W
-- statement:
--   Total correctness of `<curve25519_dalek::montgomery::ProjectivePoint>::as_affine` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`montProjectiveAsAffineSpec`): `x8` holds the address `out` of a 32-byte result buffer and `x0` the address of an 80-byte `ProjectivePoint` $(U : W)$, two `FieldElement51`s with every limb below $2^{54}$ (`montProjBounded`). The caller owns both buffers and the 1,312 bytes below the stack pointer. The postcondition: `out` holds the 32 little-endian bytes of $U \cdot W^{p-2} \bmod p$, with $U, W$ the values mod $p$; the point and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/montgomery.rs, lines 403–408: “Dehomogenize this point to affine coordinates.” It returns “$u = U / W$ if $W \neq 0$; $0$ if $W = 0$;”
--
--   **Replaces** `X25519Dalek.fnOk_projectivePoint_as_affine`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/montgomery.rs, lines 403–409 (as_affine)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_projectivePoint_as_affine_v2 :
    fnOk
      "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine"
      (fun _ => montProjectiveAsAffineSpec) := by
  sorry

end X25519Dalek
