-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_montgomeryPoint_mul
-- name    : X25519Dalek.fnOk_montgomeryPoint_mul
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T22:24:01.106409+00:00
-- url     : https://prove2.me/theorems/0a246f25-34e9-4d92-897f-d064bac1ebad
-- title:
--   Mul<&Scalar> for &MontgomeryPoint — the compiled Montgomery ladder
-- statement:
--   Total correctness of `<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`montgomeryPointMulSpec`): `x8` holds the address `out` of a 32-byte result buffer, `x0` the address of 32 bytes $u$ (`self`) and `x1` the address of 32 bytes $n$ (the `Scalar`). The caller owns the three buffers, the read-only constants `FieldElement51::ONE` and $121666$, and the 1,680 bytes below the stack pointer. No condition is placed on $n$. The postcondition: `out` holds the 32 little-endian bytes of $U \cdot W^{p-2} \bmod p$, where $(U : W)$ is `montLadderLoop 255` $n$ $u_1$ $(1 : 0)$ $(u_1 : 1)$, $u_1$ the decoded $u$ (`decodeU255`, top bit masked) mod $p$, and $n$ read as a little-endian integer; the ladder processes bits $254, \dots, 0$ of $n$. Everything else is handed back.
--
--   curve25519-dalek 5.0.0, src/montgomery.rs, line 487: “Given `self` $= u_0(P)$, and a `Scalar` $n$, return $u_0([n]P)$”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/montgomery.rs, lines 484–491 (Mul<&Scalar> for &MontgomeryPoint)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_montgomeryPoint_mul :
    fnOk
      "<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul"
      montgomeryPointMulSpec := by
  sorry

end X25519Dalek
