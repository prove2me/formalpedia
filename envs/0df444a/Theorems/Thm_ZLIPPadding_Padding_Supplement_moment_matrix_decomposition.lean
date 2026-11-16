-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_moment_matrix_decomposition
-- name    : ZLIPPadding.Padding.Supplement.moment_matrix_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:20:11.766391+00:00
-- url     : https://prove2.me/theorems/cc695484-2d8b-42d4-93f6-d4addd106cdb
-- title:
--   Proposition 4.2 — Fourth-moment matrix decomposition
-- statement:
--   Let $n\ge2$, $m\ge1$, $O\in O(n)$ and suppose $S_m(\mathbb Z^n)$ is nonempty. Let $Y$ be uniform on $S_m(L)$, where $L=O\mathbb Z^n$, and let the prescribed query be $x=Oa\in S_m(L)$. Define $C_x=\mathbb E[YY^\top\langle x,Y\rangle^2]$, $K_x=mI+2xx^\top$ and $D_x=\sum_i a_i^2(Oe_i)(Oe_i)^\top$. For the signed uniform-shell moments $\beta$ and $\kappa$,
--
--   $$C_x=\beta K_x+\kappa D_x.$$
--
--   This identifies the population matrix whose eigenvalue multiset records the entire orbit label, without supplying the hidden basis to the algorithm.
--
--   Differences from the source:
--   - encoding: ambient vectors in the rotated lattice → real Euclidean vectors Oa indexed by Fin n and a uniform PMF on the standard shell; reason: orthogonal transport gives exactly the same shell and moment matrix
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 17 (PDF p. 18), Proposition 4.2

import Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem moment_matrix_decomposition (n m : ℕ) (hn : 2 ≤ n)
    (hm : 1 ≤ m) (O : RMat n) (hO : Orthogonal O)
    (μ : PMF (ZVec n)) (hμ : UniformOn μ (shell n m))
    (a : ZVec n) (ha : a ∈ shell n m) :
    momentC O m μ (rotate O (liftZ a)) =
      shellBeta n m • queryK m (rotate O (liftZ a)) +
        shellKappa n m • coordinateD O a := by sorry

end ZLIPPadding.Padding.Supplement
