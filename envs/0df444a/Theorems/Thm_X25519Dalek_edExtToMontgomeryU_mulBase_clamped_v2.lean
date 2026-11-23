-- Prove2me | Theorems.Thm_X25519Dalek_edExtToMontgomeryU_mulBase_clamped_v2
-- name    : X25519Dalek.edExtToMontgomeryU_mulBase_clamped_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:22.127399+00:00
-- url     : https://prove2.me/theorems/16d1799a-e423-40ce-a66f-2225ca975e57
-- title:
--   curve25519-dalek's fixed-base multiplication followed by to_montgomery computes X25519(k, 9)
-- statement:
--   For every list $s$ of 32 bytes: run curve25519-dalek's fixed-base scalar multiplication on edwards25519 with the library's precomputed basepoint table (`edMulBase ed25519BasepointTableBytes`, the radix-16 signed-digit algorithm of `EdwardsBasepointTable::mul_base`) on the clamped scalar `clampScalarBytes s`, take the Montgomery $u$-coordinate $(Z + Y)/(Z - Y) \bmod p$ of the resulting extended point (`edExtToMontgomeryU`, as `EdwardsPoint::to_montgomery` computes it), and encode it as 32 little-endian bytes. The result is RFC 7748's public key `x25519Pubkey s` $= \mathrm{X25519}(s, 9)$.
--
--   The functions are those of the mission bundles `X25519Dalek_Spec` (the table bytes, `edMulBase`, `edExtToMontgomeryU`) and `X25519Dalek_Rfc7748` (clamping, `natToLeBytes`, `x25519Pubkey`), transcribed from google-deepmind/code-verification @ 8c8d371f. The statement is DeepMind's `edExtToMontgomeryU_mulBase_clamped` (PubFromSecretMath.lean), which they prove from the validity of the table (every entry is the stated multiple of the basepoint), the correctness of the signed radix-16 recoding, the birational map from edwards25519 to Curve25519, and the identification of $\mathrm{X25519}(k, 9)$ with the $u$-coordinate of $[\mathrm{clamp}(k)]B$. It is the functional half of the contract of `PublicKey::from(&StaticSecret)` in the x25519-dalek mission; the hypothesis $|s| = 32$ is the contract's.
--
--   **Replaces** `X25519Dalek.edExtToMontgomeryU_mulBase_clamped`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), LibsignalBinary/Proofs/HookDischarge/CryptoX25519/PubFromSecretMath.lean, theorem edExtToMontgomeryU_mulBase_clamped, https://github.com/google-deepmind/code-verification

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem edExtToMontgomeryU_mulBase_clamped_v2 (s : List (BitVec 8)) (hs : s.length = 32) :
    natToLeBytes 32
        (edExtToMontgomeryU (edMulBase ed25519BasepointTableBytes (clampScalarBytes s))) =
      x25519Pubkey s := by
  sorry

end X25519Dalek
