-- Prove2me | Theorems.Thm_X25519Dalek_subroutineOk_diffie_hellman
-- name    : X25519Dalek.subroutineOk_diffie_hellman
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T22:49:20.033384+00:00
-- url     : https://prove2.me/theorems/c011a5c1-36af-42f6-ba9d-54893097c589
-- title:
--   StaticSecret::diffie_hellman — the compiled code computes X25519(self, their_public)
-- statement:
--   Total correctness of `<x25519_dalek::x25519::StaticSecret>::diffie_hellman` in the AArch64 object code of x25519-dalek 3.0.0 and curve25519-dalek 5.0.0 (`x25519CliMultiLib`, exported function). For every placement of the library's 19 code blocks and 3 constants that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates. It returns to the caller (the link register) with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding. It never panics, exits or runs out of memory.
--
--   The precondition (`staticSecretDiffieHellmanSpec`): `x8` holds the address `out` of a 32-byte result buffer, `x0` the address of the 32 bytes $k$ of the `StaticSecret`, and `x1` the address of the 32 bytes $u$ of the `PublicKey`. The caller owns these three buffers (any contents in `out`), the two read-only constants `FieldElement51::ONE` and $121666$ at their placed addresses, and the 1,808 bytes below the stack pointer (any contents). The postcondition: `out` holds $\mathrm{X25519}(k, u)$, computed by RFC 7748's function `x25519` (bundle `X25519Dalek_Rfc7748`): $k$ clamped, $u$ read little-endian with its top bit masked, the Montgomery ladder, and the result as 32 little-endian bytes. The secret, the public key, the two constants and the stack frame are handed back; the stack frame's contents may have changed.
--
--   x25519-dalek 3.0.0, src/x25519.rs, lines 210–211: “Perform a Diffie-Hellman key agreement between `self` and `their_public` key to produce a `SharedSecret`.” RFC 7748, §6.1: “Using their generated values and the received input, Alice computes X25519(a, K_B) and Bob computes X25519(b, K_A).”
-- source:
--   x25519-dalek 3.0.0 (https://crates.io/crates/x25519-dalek/3.0.0), src/x25519.rs, lines 210–213 (StaticSecret::diffie_hellman)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem subroutineOk_diffie_hellman :
    x25519CliMultiLib.subroutineOk
      "<x25519_dalek::x25519::StaticSecret>::diffie_hellman"
      staticSecretDiffieHellmanSpec := by
  sorry

end X25519Dalek
