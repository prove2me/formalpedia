-- Prove2me | Theorems.Thm_mme_boundary_dims_le_seven_pow
-- name    : mme_boundary_dims_le_seven_pow
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-19T17:22:54.966397+00:00
-- url     : https://prove2.me/theorems/6023574c-d8ed-4b5e-ab66-9c87512aca77
-- title:
--   Boundary dimensions multiply to at most 7^N
-- statement:
--   Fix any level and size in the More Asymmetry regional setting. For every finite boundary end B, the product of its three matrix dimensions is at most seven to the power of the size. In particular $$a(B)b(B)c(B) \le 7^N.$$ Each part contributes its profile dimension, a multinomial coefficient times a power of five, to exactly one of the three coordinates. Summing the multinomial expansion over all count vectors and factoring the word sum position by position gives seven per elementary position. This caps what boundary-only recipes can ever deliver toward any surplus inequality. Formalization Note Lean states the bound with explicit level, size and predicate binders over BoundaryEnd.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Dimension counting for boundary profiles via the multinomial theorem.

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_recursive_yz_cell_partition
open MME MME.ProfiledCW MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_boundary_dims_le_seven_pow : forall (ell N : Nat) (P : MME.ProfiledCW.Predicate N) (B : MME.ProfiledCW.BoundaryEnd ell N P), B.a * B.b * B.c <= 7 ^ N := by sorry
