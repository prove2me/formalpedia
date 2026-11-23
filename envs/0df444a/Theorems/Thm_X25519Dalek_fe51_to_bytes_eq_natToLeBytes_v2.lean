-- Prove2me | Theorems.Thm_X25519Dalek_fe51_to_bytes_eq_natToLeBytes_v2
-- name    : X25519Dalek.fe51_to_bytes_eq_natToLeBytes_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:20.249015+00:00
-- url     : https://prove2.me/theorems/8354f0fb-14e9-465a-b579-9f91c789746a
-- title:
--   The carry chains and byte packing of FieldElement51::to_bytes give the canonical 32-byte encoding mod p
-- statement:
--   Let $l_0, \dots, l_4$ be 64-bit words with $l_i < 2^{54}$ (as natural numbers), representing the field element $\mathrm{fe51Val}(l) = l_0 + 2^{51} l_1 + 2^{102} l_2 + 2^{153} l_3 + 2^{204} l_4$, and $p = 2^{255} - 19$. All operations below are on 64-bit words (wrapping), with $m = 2^{51} - 1$:
--
--   - the first carry chain $h_0 = (l_0 \mathbin{\&} m) + 19 \cdot (l_4 \gg 51)$ (the shifted value truncated to 32 bits and zero-extended), $h_i = (l_i \mathbin{\&} m) + (l_{i-1} \gg 51)$ for $i = 1, \dots, 4$;
--   - the quotient $q = (h_4 + (h_3 + (h_2 + (h_1 + (h_0 + 19) \gg 51) \gg 51) \gg 51) \gg 51) \gg 51$;
--   - the second carry chain $u_0 = h_0 + 19 q$ ($q$ truncated to 32 bits and zero-extended), $u_i = h_i + (u_{i-1} \gg 51)$ for $i = 1, \dots, 4$.
--
--   Then the 32 bytes listed in the statement — the low byte of $u_0, u_0 \gg 8, \dots$, with the four bytes that straddle two limbs formed from the 32-bit truncations as the compiled code does — are exactly $\mathrm{natToLeBytes}_{32}(\mathrm{fe51Val}(l) \bmod p)$, the canonical little-endian encoding of the value modulo $p$.
--
--   This is the arithmetic of curve25519-dalek's `FieldElement51::to_bytes` as compiled for AArch64 (inlined in `ProjectivePoint::as_affine`, block 11 of the mission's object code): the operations and the byte expressions are the ones the instructions compute. Note that the bytes are built from the $u_i$ without masking them to 51 bits; the high bits of $u_i$ are shifted out of each byte. It is DeepMind's `fe51_to_bytes_math` (google-deepmind/code-verification @ 8c8d371f, `Shared51/Field51Base.lean`) with DeepMind's `packCanonical51Bytes` written out as the list.
--
--   **Replaces** `X25519Dalek.fe51_to_bytes_eq_natToLeBytes`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/Field51Base.lean, theorem fe51_to_bytes_math, https://github.com/google-deepmind/code-verification

import Mathlib.Algebra.Group.Nat.Defs
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fe51_to_bytes_eq_natToLeBytes_v2 (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54) (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51) (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51) (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51)
    (hu0 : u0 = h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64)
    (hu1 : u1 = h1 + u0 >>> 51) (hu2 : u2 = h2 + u1 >>> 51) (hu3 : u3 = h3 + u2 >>> 51) (hu4 : u4 = h4 + u3 >>> 51) :
    [BitVec.zeroExtend 8 u0, BitVec.zeroExtend 8 (u0 >>> 8), BitVec.zeroExtend 8 (u0 >>> 16),
      BitVec.zeroExtend 8 (u0 >>> 24), BitVec.zeroExtend 8 (u0 >>> 32), BitVec.zeroExtend 8 (u0 >>> 40),
      BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (u0 >>> 48)) &&& 18446744069414584327#64 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 u1) &&& 536870911#64) <<< 3),
      BitVec.zeroExtend 8 (u1 >>> 5), BitVec.zeroExtend 8 (u1 >>> 13), BitVec.zeroExtend 8 (u1 >>> 21),
      BitVec.zeroExtend 8 (u1 >>> 29), BitVec.zeroExtend 8 (u1 >>> 37),
      BitVec.truncate 8 (BitVec.setWidth 32 (u1 >>> 45 &&& 63#64) ||| BitVec.setWidth 32 u2 <<< 6),
      BitVec.zeroExtend 8 (u2 >>> 2), BitVec.zeroExtend 8 (u2 >>> 10), BitVec.zeroExtend 8 (u2 >>> 18),
      BitVec.zeroExtend 8 (u2 >>> 26), BitVec.zeroExtend 8 (u2 >>> 34), BitVec.zeroExtend 8 (u2 >>> 42),
      BitVec.truncate 8 (BitVec.setWidth 32 (u2 >>> 50 &&& 1#64) ||| BitVec.setWidth 32 u3 <<< 1),
      BitVec.zeroExtend 8 (u3 >>> 7), BitVec.zeroExtend 8 (u3 >>> 15), BitVec.zeroExtend 8 (u3 >>> 23),
      BitVec.zeroExtend 8 (u3 >>> 31), BitVec.zeroExtend 8 (u3 >>> 39),
      BitVec.truncate 8 (BitVec.setWidth 32 (u3 >>> 47 &&& 15#64) ||| BitVec.setWidth 32 u4 <<< 4),
      BitVec.zeroExtend 8 (u4 >>> 4), BitVec.zeroExtend 8 (u4 >>> 12), BitVec.zeroExtend 8 (u4 >>> 20),
      BitVec.zeroExtend 8 (u4 >>> 28), BitVec.zeroExtend 8 (u4 >>> 36), BitVec.zeroExtend 8 (u4 >>> 44 &&& 127#64)]
      = natToLeBytes 32 (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  sorry

end X25519Dalek
