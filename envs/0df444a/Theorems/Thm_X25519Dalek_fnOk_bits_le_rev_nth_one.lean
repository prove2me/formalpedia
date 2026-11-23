-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_bits_le_rev_nth_one
-- name    : X25519Dalek.fnOk_bits_le_rev_nth_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T21:41:35.035839+00:00
-- url     : https://prove2.me/theorems/e954c686-8bc7-43c3-a361-6b465bc7c743
-- title:
--   Rev::nth on Scalar::bits_le at n = 1 — the compiled read of scalar bit 254
-- statement:
--   Total correctness of `<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`), for the argument $n = 1$ on a fresh iterator. For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`revNthBit254Spec`): `x0` holds the address `iter` of the iterator, whose three 64-bit words are a pointer to 32 scalar bytes $s$ (owned by the caller), the range start $0$ and the range end $256$; `x1` holds $n = 1$. The caller owns the iterator's words, the scalar bytes and the 16 bytes below the stack pointer. The postcondition: the range end is now $254$, the first two words and $s$ are unchanged, and the low 8 bits of `w0` are bit 254 of $s$ read as a little-endian integer ($\lfloor s / 2^{254} \rfloor \bmod 2$).
--
--   Rust 1.98.1, library/core/src/iter/traits/iterator.rs, lines 346–349: “Returns the `n`th element of the iterator. Like most indexing operations, the count starts from zero, so `nth(0)` returns the first value, `nth(1)` the second, and so on.”
-- source:
--   Rust 1.98.1, library/core (https://github.com/rust-lang/rust/tree/1.98.1/library/core), src/iter/traits/iterator.rs, lines 346–349 (Iterator::nth), as called from curve25519-dalek 5.0.0 src/montgomery.rs, line 491

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_bits_le_rev_nth_one :
    fnOk
      "<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth"
      (fun _ => revNthBit254Spec) := by
  sorry

end X25519Dalek
