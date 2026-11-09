-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_hidden_signed_permutations
-- name    : ZLIPPadding.Padding.hidden_signed_permutations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:57.224712+00:00
-- url     : https://prove2.me/theorems/85a05fc8-c895-4859-be5b-7ba9ed49a74a
-- title:
--   Lemma 2.2 — Hidden signed permutations
-- statement:
--   Let $n$ be positive, $O$ an arbitrary real orthogonal matrix, and $L=O\mathbb Z^n$. Let $B_n$ be the full group of signed permutation matrices. Then
--   $$\operatorname{Aut}(L)=OB_nO^T.$$
--   Here automorphisms are orthogonal linear maps preserving the whole lattice. Both inclusions are asserted. This identifies the support permutations used in the projection analysis.
--
--   Differences from the source: none.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 8 (PDF p. 9), Lemma 2.2

import Definitions.Def_ZLIPPadding_Padding_GramModel

namespace ZLIPPadding.Padding
/-- Lemma 2.2, printed p.8 / PDF p.9. The ambient rotation is arbitrary real orthogonal. -/
theorem hidden_signed_permutations (n : ℕ) (hn : 0 < n)
    (O : RMat n) (hO : Orthogonal O) :
    latticeAut O = (fun P => O * P * O.transpose) '' signedMatrices n := by sorry
end ZLIPPadding.Padding
