-- Prove2me | Theorems.Thm_X25519Dalek_x25519Pubkey_eq_edToMontU
-- name    : X25519Dalek.x25519Pubkey_eq_edToMontU
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T22:38:58.855939+00:00
-- url     : https://prove2.me/theorems/f04d7952-23cc-405a-b9d3-c9a922d5a169
-- title:
--   RFC 7748 §4.1 — the public key X25519(s, 9) is u((1 + y)/(1 − y)) of the Edwards multiple [s]B
-- statement:
--   For every byte list $s$, `x25519Pubkey s` (RFC 7748's $\mathrm{X25519}(s, 9)$) is the 32 little-endian bytes of $(1 + y)(1 - y)^{p-2} \bmod p$ (`edToMontU`), where $(x, y)$ = `edSmul (clampScalar s) edBasepoint`: the clamped scalar of $s$ times the edwards25519 base point $(X(P), Y(P))$ of RFC 7748 §4.1, computed by double-and-add with the extended-coordinate addition formulas of RFC 8032 §5.1.4 and returned in affine coordinates.
--
--   RFC 7748, §4.1: “This curve is birationally equivalent to a twisted Edwards curve -x^2 + y^2 = 1 + d*x^2*y^2, called "edwards25519"” […] “The birational maps are: (u, v) = ((1+y)/(1-y), sqrt(-486664)*u/x)”
-- source:
--   A. Langley, M. Hamburg and S. Turner, Elliptic Curves for Security, RFC 7748, January 2016, https://doi.org/10.17487/RFC7748, §4.1, the birational map to edwards25519 (p. 1 of the excerpts)

import Mathlib
import Definitions.Def_X25519Dalek_Rfc7748

namespace X25519Dalek

theorem x25519Pubkey_eq_edToMontU (s : List (BitVec 8)) :
    x25519Pubkey s = natToLeBytes 32 (edToMontU (edSmul (clampScalar s) edBasepoint)) := by
  sorry

end X25519Dalek
