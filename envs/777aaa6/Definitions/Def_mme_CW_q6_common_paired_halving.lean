-- Prove2me | Definitions.Def_mme_CW_q6_common_paired_halving
-- name    : mme_CW_q6_common_paired_halving
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T10:38:42.948389+00:00
-- url     : https://prove2.me/theorems/3a390409-886c-4aef-8411-face36316a56
-- title:
--   A family-wide balanced halving for paired coupled-CW sources
-- statement:
--   Let a primary coupled-$q=6$ hash family consist of address triples on $2N$ tensor-power positions. A common balanced $XY$ halving is one bijection
--
--   $$e:[N]\sqcup[N]\longrightarrow[2N]$$
--
--   shared by every entry of the family, together with $N=2n$, such that every entry has exactly $n$ zeroes and $n$ ones in its first-mode word on the first half, and exactly $n$ zeroes and $n$ ones in its second-mode word on the second half. No condition is imposed on the two unused half-marginals.
--
--   The module also defines simultaneous position reindexing of a coupled address. The requirement that the same $e$ works for the whole family is essential: it preserves the induced-family condition under reindexing and makes both words land in the equal-split allowed-word spaces of the paired Table-2 $121/211$ source. Independently chosen halvings for different entries do not have this property.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent and primary pruning on journal pp. 266-271; Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2-5.4 and the rotated 121/211 component analysis in Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_q6_primary_hash_family

namespace MME

def cwQ6CoupledAddressPositionReindex {N : ℕ}
    (rho : Equiv.Perm (Fin (2 * N)))
    (address : CWQ6CoupledAddress N) : CWQ6CoupledAddress N :=
  fun i j ↦ address i (rho j)

structure CWQ6PrimaryHashFamily.CommonBalancedXYHalving
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H) where
  half : ℕ
  even_length : N = 2 * half
  position : (Fin N ⊕ Fin N) ≃ Fin (2 * N)
  first_x : ∀ (p : Fin A × Fin H) (grade : Fin 3),
    Fintype.card {j : Fin N //
      (family.entry p).1 0 (position (Sum.inl j)) = grade} =
        if grade = 0 then half else if grade = 1 then half else 0
  second_y : ∀ (p : Fin A × Fin H) (grade : Fin 3),
    Fintype.card {j : Fin N //
      (family.entry p).1 1 (position (Sum.inr j)) = grade} =
        if grade = 0 then half else if grade = 1 then half else 0

end MME


