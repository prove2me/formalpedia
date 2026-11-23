-- Prove2me | Theorems.Thm_X25519Dalek_subroutineOk_diffie_hellman_v2
-- name    : X25519Dalek.subroutineOk_diffie_hellman_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:15.111506+00:00
-- url     : https://prove2.me/theorems/3f0ca5eb-2640-4df4-9ee6-96ddf7c424fc
-- title:
--   StaticSecret::diffie_hellman — the compiled code computes X25519(self, their_public)
-- statement:
--   Total correctness of `<x25519_dalek::x25519::StaticSecret>::diffie_hellman` in the AArch64 object code of x25519-dalek 3.0.0 and curve25519-dalek 5.0.0 (`x25519CliMultiLib`, exported function). For every placement of the library's 19 code blocks and 3 constants that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates. It returns to the caller (the link register) with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding. It never panics, exits or runs out of memory.
--
--   The precondition (`staticSecretDiffieHellmanSpec`): `x8` holds the address `out` of a 32-byte result buffer, `x0` the address of the 32 bytes $k$ of the `StaticSecret`, and `x1` the address of the 32 bytes $u$ of the `PublicKey`. The caller owns these three buffers (any contents in `out`), the two read-only constants `FieldElement51::ONE` and $121666$ at their placed addresses, and the 1,808 bytes below the stack pointer (any contents). The postcondition: `out` holds $\mathrm{X25519}(k, u)$, computed by RFC 7748's function `x25519` (bundle `X25519Dalek_Rfc7748`): $k$ clamped, $u$ read little-endian with its top bit masked, the Montgomery ladder, and the result as 32 little-endian bytes. The secret, the public key, the two constants and the stack frame are handed back; the stack frame's contents may have changed.
--
--   x25519-dalek 3.0.0, src/x25519.rs, lines 210–211: “Perform a Diffie-Hellman key agreement between `self` and `their_public` key to produce a `SharedSecret`.” RFC 7748, §6.1: “Using their generated values and the received input, Alice computes X25519(a, K_B) and Bob computes X25519(b, K_A).”
--
--   **Replaces** `X25519Dalek.subroutineOk_diffie_hellman`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   x25519-dalek 3.0.0 (https://crates.io/crates/x25519-dalek/3.0.0), src/x25519.rs, lines 210–213 (StaticSecret::diffie_hellman)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem subroutineOk_diffie_hellman_v2 :
    x25519CliMultiLib.subroutineOk
      "<x25519_dalek::x25519::StaticSecret>::diffie_hellman"
      staticSecretDiffieHellmanSpec := by
  sorry

end X25519Dalek
