-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_fe51_pow2k_v2
-- name    : X25519Dalek.fnOk_fe51_pow2k_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:04.593471+00:00
-- url     : https://prove2.me/theorems/fb77ebea-cdd2-40ac-84db-7d631a06232f
-- title:
--   FieldElement51::pow2k — the compiled x^(2^k)
-- statement:
--   Total correctness of `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`fe51Pow2kSpec`): `x8` holds the address `out` of a 40-byte result buffer, `x0` the address of a 40-byte `FieldElement51` $x$ with every limb below $2^{54}$, and the low 32 bits of `x1` are $k$ with $0 < k < 256$. The caller owns both buffers and the 96 bytes below the stack pointer. The postcondition: `out` holds a `FieldElement51` with every limb below $2^{52}$ whose value mod $p$ is $x^{2^k} \bmod p$ (`fpPow`), with $x$ the input's value mod $p$. The input and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/backend/serial/u64/field.rs, line 452: “Given `k > 0`, return `self^(2^k)`.”
--
--   **Replaces** `X25519Dalek.fnOk_fe51_pow2k`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/backend/serial/u64/field.rs, lines 452–454 (pow2k)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_fe51_pow2k_v2 :
    fnOk
      "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k"
      (fun _ => fe51Pow2kSpec) := by
  sorry

end X25519Dalek
