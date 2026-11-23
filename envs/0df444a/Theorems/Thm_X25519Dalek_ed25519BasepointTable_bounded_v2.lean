-- Prove2me | Theorems.Thm_X25519Dalek_ed25519BasepointTable_bounded_v2
-- name    : X25519Dalek.ed25519BasepointTable_bounded_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:19.786709+00:00
-- url     : https://prove2.me/theorems/8ce04b7f-f069-4b1e-846b-6c256cda6a12
-- title:
--   Every limb of curve25519-dalek's basepoint table is below 2^52
-- statement:
--   The 30,720 read-only bytes `ed25519BasepointTableBytes` of curve25519-dalek's precomputed table `ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN` (as placed in the x25519-dalek mission's object, bundle `X25519Dalek_PlacedObj`) form 32 lookup tables of 960 bytes; each lookup table is 8 `AffineNielsPoint` entries of 120 bytes; each entry is 3 field elements of 40 bytes; each field element is 5 little-endian 64-bit limbs. The statement is `fe51BasepointTable32Bounded ed25519BasepointTableBytes (2 ^ 52)` of the bundle `X25519Dalek_Spec`: the table has length 30,720, and for every $i < 32$ the 960-byte slice at offset $960 i$ has length 960 and every one of its 120 limbs (all 5 limbs of all 3 field elements of all 8 entries) is $< 2^{52}$.
--
--   `EdwardsBasepointTable::mul_base`'s contract in the mission asks for the weaker bound $2^{53}$ on the table it is given; `EdwardsPoint::mul_base_clamped` passes this table, so the bound is a step of that function's proof. The statement is DeepMind's `ed25519BasepointTableBytes_bounded` (google-deepmind/code-verification @ 8c8d371f, Shared51/InternalSpecs.lean), a finite check over the 3,840 limbs.
--
--   **Replaces** `X25519Dalek.ed25519BasepointTable_bounded`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/InternalSpecs.lean, theorem ed25519BasepointTableBytes_bounded, https://github.com/google-deepmind/code-verification

import Mathlib.Algebra.Group.Nat.Defs
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem ed25519BasepointTable_bounded_v2 :
    fe51BasepointTable32Bounded ed25519BasepointTableBytes (2 ^ 52) := by
  sorry

end X25519Dalek
