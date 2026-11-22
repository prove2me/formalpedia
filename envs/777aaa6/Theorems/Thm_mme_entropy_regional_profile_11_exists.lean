-- Prove2me | Theorems.Thm_mme_entropy_regional_profile_11_exists
-- name    : mme_entropy_regional_profile_11_exists
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-15T19:51:25.333904+00:00
-- url     : https://prove2.me/theorems/cfc44236-569f-406b-b3a1-134ff7886dd9
-- title:
--   Level-two (1,1)-profile has dimension 25
-- statement:
--   The level-two boundary profile on the word $(1,1)$ exists and has dimension $25$. At level $\ell = 2$ with a single position, the profile counting the word $(1,1)$ once has multinomial coefficient $1$ and $5$-power $5^2$, giving $$\dim = 25.$$ This is the boundary profile feeding the More Asymmetry regional construction: its dimensions $(5,5,1)$ multiply to $25$. **Formalization Note** Lean states existence of a `Boundary.Profile 2 1` of dimension $25$.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Section 6 regional construction; the level-two profile on the word (1,1) contributes 5^2=25 dimensions

import Definitions.Def_mme_recursive_yz_boundary_data

set_option autoImplicit false

theorem mme_entropy_regional_profile_11_exists :
    exists (prof : MME.RecursiveYZ.Boundary.Profile 2 1), prof.dim = 25 := by sorry
