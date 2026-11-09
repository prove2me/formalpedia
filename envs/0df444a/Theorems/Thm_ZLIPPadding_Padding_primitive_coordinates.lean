-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_primitive_coordinates
-- name    : ZLIPPadding.Padding.primitive_coordinates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:46.134611+00:00
-- url     : https://prove2.me/theorems/86c7c4ac-542d-41bb-823b-04d5bcb70e71
-- title:
--   Lemma 7.3 — Primitive coordinates
-- statement:
--   Let $n$ be positive, $M\in\mathrm{GL}_n(\mathbb Z)$ and $a\in\mathbb Z^n\setminus\{0\}$. Taking the positive gcd of all coordinates,
--   $$\gcd(Ma)=\gcd(a).$$
--   Arbitrary signs, repeated coordinates and nonprimitive vectors are included. The assertion is for unimodular changes of a basis of the whole lattice.
--
--   Differences from the source: none.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 30 (PDF p. 31), Lemma 7.3

import Definitions.Def_ZLIPPadding_Padding_GramModel

namespace ZLIPPadding.Padding
/-- Lemma 7.3, printed p.30 / PDF p.31. -/
theorem primitive_coordinates (n : ℕ) (hn : 0 < n) (M : ZMat n)
    (hM : Unimodular M) (a : ZVec n) (ha : a ≠ 0) :
    coordGcd (M.mulVec a) = coordGcd a := by sorry
end ZLIPPadding.Padding
