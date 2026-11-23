-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_mul_by_pow_2_four_v2
-- name    : X25519Dalek.fnOk_edwardsPoint_mul_by_pow_2_four_v2
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-23T19:13:59.975957+00:00
-- url     : https://prove2.me/theorems/4bca812f-6767-4eea-b994-a6e074b3492a
-- title:
--   EdwardsPoint::mul_by_pow_2 at k = 4 — the compiled four successive doublings
-- statement:
--   Total correctness of `<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`), for the argument $k = 4$. For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`edwardsPointMulByPow2_4Spec`): `x8` holds the address `out` of a 160-byte result buffer, `x0` the address of a 160-byte `EdwardsPoint` with every limb below $2^{53}$, and the low 32 bits of `x1` are $k = 4$. The caller owns both buffers and the 912 bytes below the stack pointer. The postcondition: `out` holds an `EdwardsPoint` with every limb below $2^{52}$ whose coordinates mod $p$ are `edDouble4` of the input's: three rounds of `ProjectivePoint::double` followed by conversion to projective coordinates, then a fourth doubling converted to extended coordinates. The input and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/edwards.rs, line 1369: “Compute $[2^k] P$ by successive doublings. Requires $k > 0$.”
--
--   **Replaces** `X25519Dalek.fnOk_edwardsPoint_mul_by_pow_2_four`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/edwards.rs, lines 1369–1370 (mul_by_pow_2)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_edwardsPoint_mul_by_pow_2_four_v2 :
    fnOk
      "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2"
      (fun _ => edwardsPointMulByPow2_4Spec) := by
  sorry

end X25519Dalek
