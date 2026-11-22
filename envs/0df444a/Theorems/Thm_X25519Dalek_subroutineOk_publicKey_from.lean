-- Prove2me | Theorems.Thm_X25519Dalek_subroutineOk_publicKey_from
-- name    : X25519Dalek.subroutineOk_publicKey_from
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T22:29:30.8258+00:00
-- url     : https://prove2.me/theorems/6d61ab26-b2c1-43a0-92ad-4202ce640044
-- title:
--   PublicKey::from(&StaticSecret) — the compiled code computes X25519(secret, 9)
-- statement:
--   Total correctness of `<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from` in the AArch64 object code of x25519-dalek 3.0.0 and curve25519-dalek 5.0.0 (`x25519CliMultiLib`, exported function). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates. It returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding. It never panics, exits or runs out of memory.
--
--   The precondition (`publicKeyFromSecretSpec`): `x8` holds the address `out` of a 32-byte result buffer and `x0` the address of the 32 bytes $k$ of the `StaticSecret`. The caller owns both buffers (any contents in `out`), the read-only constants `ED25519_BASEPOINT_TABLE` (30,720 bytes) and `FieldElement51::ONE` at their placed addresses, and the 1,904 bytes below the stack pointer. The postcondition: `out` holds `x25519Pubkey` $k$ $= \mathrm{X25519}(k, 9)$ of RFC 7748 (bundle `X25519Dalek_Rfc7748`); the secret, the constants and the stack frame are handed back.
--
--   x25519-dalek 3.0.0, src/x25519.rs, line 256: “Given an x25519 [`StaticSecret`] key, compute its corresponding [`PublicKey`].” RFC 7748, §6.1: “Alice generates 32 random bytes in a[0] to a[31] and transmits K_A = X25519(a, 9) to Bob, where 9 is the u-coordinate of the base point and is encoded as a byte with value 9, followed by 31 zero bytes.”
-- source:
--   x25519-dalek 3.0.0 (https://crates.io/crates/x25519-dalek/3.0.0), src/x25519.rs, lines 255–259 (From<&StaticSecret> for PublicKey)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem subroutineOk_publicKey_from :
    x25519CliMultiLib.subroutineOk
      "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"
      publicKeyFromSecretSpec := by
  sorry

end X25519Dalek
