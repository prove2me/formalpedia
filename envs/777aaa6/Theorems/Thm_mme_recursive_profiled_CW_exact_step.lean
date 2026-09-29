-- Prove2me | Theorems.Thm_mme_recursive_profiled_CW_exact_step
-- name    : mme_recursive_profiled_CW_exact_step
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:53:16.840405+00:00
-- url     : https://prove2.me/theorems/a5b70115-57bf-4f78-ace6-329205bb7921
-- title:
--   A finite profiled CW step realizes its counted output copies
-- statement:
--   Every ExactStep certificate yields its stated number floor(k/8^h) of independent copies of the actual output CW5 projection from the actual input projection. Both projections use the same elementary CW factor positions. All source-profile reblocking is proved from the explicit finite index equivalence; the data contains no assumed tensor map.
-- source:
--   Finite constructive realization of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorems 6.2 and 6.4; Section 7 for conversion to an exponent bound. This theorem retains explicit finite combinatorial hypotheses and input-copy costs. It does not supply the paper numerical parameter witness.

import Definitions.Def_mme_recursive_profiled_CW_data
open MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_recursive_profiled_CW_exact_step {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) :
    Restrict (bigAdd (fun _ : Fin E.copies ↦ tensor K E.output)) (tensor K P) := by sorry
