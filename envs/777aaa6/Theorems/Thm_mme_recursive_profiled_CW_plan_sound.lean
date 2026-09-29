-- Prove2me | Theorems.Thm_mme_recursive_profiled_CW_plan_sound
-- name    : mme_recursive_profiled_CW_plan_sound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:53:23.072109+00:00
-- url     : https://prove2.me/theorems/846ec254-e73d-4d41-94d8-46adc05534f4
-- title:
--   A finite descending CW profile plan yields all counted matrix copies
-- statement:
--   Every finite level-descending Plan gives an actual restriction from inputs independent copies of its profiled CW5 power to outputs independent copies of the matrix tensor with its computed dimensions. At each interior step, inputs multiply by the number of exact profile cases and outputs multiply by the common repaired-copy count. The terminal boundary dimensions are exact. All plan hypotheses concern finite hashes, profile words, coverage and hole cardinalities; no interior tensor-map hypothesis occurs in the data.
-- source:
--   Finite constructive realization of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorems 6.2 and 6.4; Section 7 for conversion to an exponent bound. This theorem retains explicit finite combinatorial hypotheses and input-copy costs. It does not supply the paper numerical parameter witness.

import Definitions.Def_mme_recursive_profiled_CW_data
open MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_recursive_profiled_CW_plan_sound {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : Plan N ell P) :
    Restrict (bigAdd (fun _ : Fin D.outputs ↦ MMObj K D.a D.b D.c))
      (bigAdd (fun _ : Fin D.inputs ↦ tensor K P)) := by sorry
