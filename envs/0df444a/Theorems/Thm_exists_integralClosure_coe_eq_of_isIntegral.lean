-- Prove2me | Theorems.Thm_exists_integralClosure_coe_eq_of_isIntegral
-- name    : exists_integralClosure_coe_eq_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/06b68d55-a761-5316-9c2f-ae9c09a249d2
-- title:
--   Integral complex numbers lie in the integral closure of ℤ
-- statement:
--   Let $z$ be a complex number which is integral over $\mathbb{Z}$, i.e. $z$ is a root of some monic polynomial with integer coefficients. The assertion is that there exists an element $a$ of the subalgebra $\mathrm{integralClosure}\ \mathbb{Z}\ \mathbb{C}$ of $\mathbb{C}$, namely the subalgebra of those complex numbers integral over $\mathbb{Z}$, whose image under the coercion to $\mathbb{C}$ equals $z$. This is nothing more than a restatement of the hypothesis in existential form: it converts the predicate `IsIntegral ℤ z` into the existence of a preimage of $z$ under the inclusion of the integral closure into $\mathbb{C}$, which is the shape required when one wants to speak of $z$ as an element of the ring of algebraic integers rather than as a complex number satisfying a property.
--
--   The statement records that the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ is precisely the set of algebraic integers, in the packaged form needed downstream. It is used by [`CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff`](thm.html#CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff), which exhibits the $q$-expansion coefficients of a normalised eigenform as elements of the ring of algebraic integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_integralClosure_coe_eq_of_isIntegral.lean

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem exists_integralClosure_coe_eq_of_isIntegral {z : ℂ} (hz : IsIntegral ℤ z) : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = z := by sorry
