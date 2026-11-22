-- Prove2me | Theorems.Thm_mme_integer_regional_step_N2_level_bound
-- name    : mme_integer_regional_step_N2_level_bound
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-15T20:03:52.445648+00:00
-- url     : https://prove2.me/theorems/49a8d02a-0a03-478b-ae6f-69cd98dfa566
-- title:
--   N=2 integer steps live below level 3
-- statement:
--   At $N=2$, every integer entropy step lives below level $3$. The length field $L \cdot 2^{lower-1} = 2$ is unsatisfiable for $lower \ge 3$, so only levels $0$, $1$ and $2$ (with $L = 2$, $2$ and $1$) can occur. This pins all $N=2$ step data, including the level-two case used by the regional construction, to finitely many levels. **Formalization Note** Lean states the bound over an arbitrary step with a trivial predicate.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, level-two regional setting; formalization observation on the IntegerStep/BoundaryEnd length fields forcing lower < 3 at N = 2

import Definitions.Def_mme_integer_regional_CW_recipe

set_option autoImplicit false

theorem mme_integer_regional_step_N2_level_bound :
    forall (lower : Nat) (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)),
      lower < 3 := by sorry
