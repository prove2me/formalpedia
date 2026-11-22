-- Prove2me | Theorems.Thm_X25519Dalek_x25519_comm
-- name    : X25519Dalek.x25519_comm
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T22:41:44.182805+00:00
-- url     : https://prove2.me/theorems/df942ffe-3713-4ca6-9786-b9ed680c0fb7
-- title:
--   RFC 7748 §6.1 — X25519(a, X25519(b, 9)) = X25519(b, X25519(a, 9))
-- statement:
--   For all byte lists $a$ and $b$ (of any length), `x25519 a (x25519Pubkey b) = x25519 b (x25519Pubkey a)`: RFC 7748's X25519 of $a$ applied to $b$'s public key $\mathrm{X25519}(b, 9)$ equals X25519 of $b$ applied to $a$'s public key.
--
--   RFC 7748, §6.1: “Both now share K = X25519(a, X25519(b, 9)) = X25519(b, X25519(a, 9)) as a shared secret.”
-- source:
--   A. Langley, M. Hamburg and S. Turner, Elliptic Curves for Security, RFC 7748, January 2016, https://doi.org/10.17487/RFC7748, §6.1, the shared secret (p. 6 of the excerpts)

import Mathlib
import Definitions.Def_X25519Dalek_Rfc7748

namespace X25519Dalek

theorem x25519_comm (a b : List (BitVec 8)) :
    x25519 a (x25519Pubkey b) = x25519 b (x25519Pubkey a) := by
  sorry

end X25519Dalek
