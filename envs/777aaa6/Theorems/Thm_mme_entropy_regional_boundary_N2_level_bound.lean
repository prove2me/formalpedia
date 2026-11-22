-- Prove2me | Theorems.Thm_mme_entropy_regional_boundary_N2_level_bound
-- name    : mme_entropy_regional_boundary_N2_level_bound
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-15T20:03:35.983186+00:00
-- url     : https://prove2.me/theorems/8c32a3a2-ec20-4bbe-83bd-26cb4b3ecb13
-- title:
--   N=2 boundary ends live below level 3
-- statement:
--   At $N=2$, every boundary end lives below level $3$. The length field $L \cdot 2^{lower-1} = 2$ is unsatisfiable for $lower \ge 3$, so only levels $0$, $1$ and $2$ (with $L = 2$, $2$ and $1$) can occur. This is the boundary-data counterpart of the step level bound. **Formalization Note** Lean states the bound over arbitrary boundary data and predicate.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, level-two regional setting; formalization observation on the IntegerStep/BoundaryEnd length fields forcing lower < 3 at N = 2

import Definitions.Def_mme_recursive_profiled_CW_data

set_option autoImplicit false

theorem mme_entropy_regional_boundary_N2_level_bound :
    forall (lower : Nat) (P : MME.ProfiledCW.Predicate 2)
      (B : MME.ProfiledCW.BoundaryEnd lower 2 P),
      lower < 3 := by sorry
