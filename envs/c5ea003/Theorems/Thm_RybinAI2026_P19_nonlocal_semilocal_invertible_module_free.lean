-- Prove2me | Theorems.Thm_RybinAI2026_P19_nonlocal_semilocal_invertible_module_free
-- name    : RybinAI2026.P19.nonlocal_semilocal_invertible_module_free
-- status  : Disproved
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:33:28.295475+00:00
-- url     : https://prove2.me/theorems/8d904f6a-f99b-4fc9-93d8-ad8c35ba64af
-- title:
--   The nonlocal case of the semilocal semiring Picard question
-- statement:
--   Let $R$ be a nonzero commutative semiring with finitely many maximal ideals, and assume that $R$ is not local. Is every invertible $R$-module free? This is precisely the remaining nonlocal case of the positive semilocal Picard-group question after the local and zero-semiring cases are removed. No assumption that the maximal ideals are subtractive is made.
-- source:
--   Junyan Xu, Picard group of semi-local or finite semirings, https://mathoverflow.net/questions/511864; Rybin problem 19, https://rybindmitry.github.io/problems/19.html. This is the nonlocal restriction of the original question, not a claim established by Borger and Jun.

import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalRing.Basic

theorem RybinAI2026.P19.nonlocal_semilocal_invertible_module_free
    (R M : Type*) [CommSemiring R] [Nontrivial R] [Finite (MaximalSpectrum R)]
    [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    (hlocal : ¬ IsLocalRing R) : Module.Free R M := by sorry
