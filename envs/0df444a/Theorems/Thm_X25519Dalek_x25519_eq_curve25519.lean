-- Prove2me | Theorems.Thm_X25519Dalek_x25519_eq_curve25519
-- name    : X25519Dalek.x25519_eq_curve25519
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T22:46:16.837966+00:00
-- url     : https://prove2.me/theorems/b4df379c-5d97-4107-a72e-c562c7466594
-- title:
--   RFC 7748 §5 — X25519 is Bernstein's Curve25519 function on the clamped scalar
-- statement:
--   Assume $2^{255} - 19$ is prime (as an instance argument). For all 32-byte lists $s$ and $u$, the little-endian integer of `x25519 s u` equals `Bernstein.curve25519` $n$ $q$ of the companion mission's bundle `Curve25519Bernstein`, with $n$ = `clampScalar s` (the clamped scalar as an integer) and $q$ = `decodeU255 u` (the $u$-coordinate as an integer, top bit masked). `Bernstein.curve25519 n q` is Bernstein's Curve25519 function on integers: the least $s' \le 2^{255} - 20$ such that $X_0(nQ) = s'$ for every point $Q$ of $y^2 = x^3 + 486662x^2 + x$ over $\mathbb{F}_{p^2}$ with $X_0(Q) = q \bmod p$.
--
--   RFC 7748, §5: “The "X25519" and "X448" functions perform scalar multiplication on the Montgomery form of the above curves.” §4.1: “The Montgomery curve defined here is equal to the one defined in [curve25519]”.
-- source:
--   A. Langley, M. Hamburg and S. Turner, Elliptic Curves for Security, RFC 7748, January 2016, https://doi.org/10.17487/RFC7748, §5, "perform scalar multiplication on the Montgomery form" (p. 2 of the excerpts)

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Definitions.Def_X25519Dalek_Rfc7748

namespace X25519Dalek

theorem x25519_eq_curve25519 [Fact Bernstein.p25519.Prime] (s u : List (BitVec 8))
    (hs : s.length = 32) (hu : u.length = 32) :
    leBytesToNat (x25519 s u) = Bernstein.curve25519 (clampScalar s) (decodeU255 u) := by
  sorry

end X25519Dalek
