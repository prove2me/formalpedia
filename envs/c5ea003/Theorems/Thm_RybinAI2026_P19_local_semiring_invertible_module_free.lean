-- Prove2me | Theorems.Thm_RybinAI2026_P19_local_semiring_invertible_module_free
-- name    : RybinAI2026.P19.local_semiring_invertible_module_free
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:33:21.957843+00:00
-- url     : https://prove2.me/theorems/29b1f10b-72ee-461b-8e73-2e9edf4fdf16
-- title:
--   Invertible modules over a local commutative semiring are free
-- statement:
--   Let $R$ be a local commutative semiring and let $M$ be an invertible $R$-module. Then $M$ is free. In fact it is isomorphic to $R$ as a module. Here local means that $R$ is nonzero and has a unique maximal ideal; additive inverses and cancellation are not assumed. This settles the local case of the semilocal Picard-group question.
-- source:
--   Borger and Jun, Facets of module theory over semirings, arXiv:2405.18645v3, Theorem 10.7 (invertible modules are Zariski-locally free of rank one), and the local-semiring consequence noted in Junyan Xu, Picard group of semi-local or finite semirings, https://mathoverflow.net/questions/511864. The direct evaluation proof follows the argument in the question's postscript.

import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalRing.Basic

theorem RybinAI2026.P19.local_semiring_invertible_module_free (R M : Type*) [CommSemiring R] [IsLocalRing R]
    [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    Module.Free R M := by sorry
