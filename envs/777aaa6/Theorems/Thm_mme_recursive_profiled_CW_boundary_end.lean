-- Prove2me | Theorems.Thm_mme_recursive_profiled_CW_boundary_end
-- name    : mme_recursive_profiled_CW_boundary_end
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:54:11.181056+00:00
-- url     : https://prove2.me/theorems/b1f96d53-be8c-4dec-a9de-de9670c2fa6e
-- title:
--   A concrete boundary endpoint yields the product matrix dimensions
-- statement:
--   A BoundaryEnd certificate yields an actual matrix-multiplication tensor with the product of all exact boundary dimensions from its CW5 input projection. The endpoint contains complementary boundary profiles and a finite partition of elementary factor positions; no matrix extraction map is assumed.
-- source:
--   Finite constructive realization of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorems 6.2 and 6.4; Section 7 for conversion to an exponent bound. This theorem retains explicit finite combinatorial hypotheses and input-copy costs. It does not supply the paper numerical parameter witness.

import Definitions.Def_mme_recursive_profiled_CW_data
open MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_recursive_profiled_CW_boundary_end {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (B : BoundaryEnd ell N P) :
    Restrict (MMObj K B.a B.b B.c) (tensor K P) := by sorry
