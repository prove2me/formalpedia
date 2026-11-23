-- Prove2me | Theorems.Thm_X25519Dalek_x25519_eq_zero_iff
-- name    : X25519Dalek.x25519_eq_zero_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T22:44:04.637813+00:00
-- url     : https://prove2.me/theorems/59e140d7-de2a-4311-a46b-bd8aa436c54f
-- title:
--   RFC 7748 §6.1 — X25519 is all-zero exactly on five input residues
-- statement:
--   For all byte lists $s$ and $u$, `x25519 s u` is the 32 zero bytes if and only if the decoded $u$-coordinate (`decodeU255 u`: the first 32 bytes, little-endian, top bit masked) reduced mod $p = 2^{255} - 19$ is one of the five residues of `lowOrderUs`: $0$, $1$,
--   $325606250916557431795983626356110631294008115727848805560023387167927233504$,
--   $39382357235489614581723060781553021112529911719440698176882885853963445705823$, and $p - 1$.
--
--   RFC 7748, §6.1: “The check for the all-zero value results from the fact that the X25519 function produces that value if it operates on an input corresponding to a point with small order, where the order divides the cofactor of the curve (see Section 7).”
-- source:
--   A. Langley, M. Hamburg and S. Turner, Elliptic Curves for Security, RFC 7748, January 2016, https://doi.org/10.17487/RFC7748, §6.1, the all-zero check (p. 6 of the excerpts)

import Mathlib
import Definitions.Def_X25519Dalek_Rfc7748

namespace X25519Dalek

theorem x25519_eq_zero_iff (s u : List (BitVec 8)) :
    x25519 s u = List.replicate 32 0#8 ↔ decodeU255 u % p25519 ∈ lowOrderUs := by
  sorry

end X25519Dalek
