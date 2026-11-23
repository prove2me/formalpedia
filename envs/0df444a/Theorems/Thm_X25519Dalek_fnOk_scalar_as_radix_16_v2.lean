-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_scalar_as_radix_16_v2
-- name    : X25519Dalek.fnOk_scalar_as_radix_16_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:08.036914+00:00
-- url     : https://prove2.me/theorems/0edd291b-9339-4e1c-b45a-0a78ef2393f0
-- title:
--   Scalar::as_radix_16 — the compiled signed radix-16 recoding
-- statement:
--   Total correctness of `<curve25519_dalek::scalar::Scalar>::as_radix_16` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`scalarAsRadix16Spec`): `x0` holds the address `out` of a 64-byte result buffer and `x1` the address of 32 scalar bytes $a$ whose last byte is at most $127$. The caller owns both buffers; the function uses no stack. The postcondition: `out` holds `scalarRadix16Digits a`, 64 signed bytes $a_0, \dots, a_{63}$ computed digit by digit from the nibbles of $a$ (low nibble first) with a carry: for $i < 63$, $a_i$ is the nibble plus the incoming carry, reduced to $[-8, 8)$ by subtracting $16$ times the outgoing carry $\lfloor(\text{nibble} + \text{carry} + 8)/16\rfloor$; $a_{63}$ is the last nibble plus the carry. The scalar is handed back.
--
--   curve25519-dalek 5.0.0, src/scalar.rs, lines 1009–1018: “Write this scalar in radix 16, with coefficients in $[-8,8)$, i.e., compute $a_i$ such that $a = a_0 + a_1 16^1 + \cdots + a_{63} 16^{63}$, with $-8 \leq a_i < 8$ for $0 \leq i < 63$ and $-8 \leq a_{63} \leq 8$. The largest value that can be decomposed like this is just over $2^{255}$. Thus, in order to not error, the top bit MUST NOT be set, i.e., `Self` MUST be less than $2^{255}$.”
--
--   **Replaces** `X25519Dalek.fnOk_scalar_as_radix_16`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/scalar.rs, lines 1009–1019 (as_radix_16)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_scalar_as_radix_16_v2 :
    fnOk
      "<curve25519_dalek::scalar::Scalar>::as_radix_16"
      (fun _ => scalarAsRadix16Spec) := by
  sorry

end X25519Dalek
