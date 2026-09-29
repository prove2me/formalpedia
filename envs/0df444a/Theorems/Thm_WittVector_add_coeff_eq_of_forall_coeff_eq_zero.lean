-- Prove2me | Theorems.Thm_WittVector_add_coeff_eq_of_forall_coeff_eq_zero
-- name    : WittVector.add_coeff_eq_of_forall_coeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/25cab683-6a20-5362-b389-195da1618741
-- title:
--   Adding a Witt vector with vanishing initial coefficients
-- statement:
--   Let $S$ be a commutative ring, let $p$ be a prime, and let $x$ and $y$ be $p$-typical Witt vectors over $S$, i.e. elements of `WittVector p S`. Let $r$ be a natural number, and suppose that the first $r$ coefficients of $x$ vanish: $x.\mathrm{coeff}\ i = 0$ for every $i < r$. The conclusion is that the first $r$ coefficients of the sum agree with those of $y$: for every $i < r$ one has $(x + y).\mathrm{coeff}\ i = y.\mathrm{coeff}\ i$. Here addition is the Witt vector ring addition, given in coordinates by the universal Witt addition polynomials, so the assertion is that the $i$-th Witt addition polynomial evaluated on the coefficients of $x$ and $y$ reduces to $y.\mathrm{coeff}\ i$ whenever all of $x.\mathrm{coeff}\ 0, \dots, x.\mathrm{coeff}\ (r-1)$ vanish. Equivalently, the set of Witt vectors whose first $r$ coefficients vanish — the image of the $r$-fold Verschiebung — acts trivially on the first $r$ coefficients by translation.
--
--   This is the elementary statement that truncation at level $r$ only sees the first $r$ coefficients and is additive, so that translating by a vector supported in degrees $\geq r$ does not disturb coefficients in degrees $< r$. It is used in the study of coefficients of multivariable formal group laws, in [`MvFormalGroup.coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope`](thm.html#MvFormalGroup.coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_add_coeff_eq_of_forall_coeff_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WittVector.add_coeff_eq_of_forall_coeff_eq_zero
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (x y : WittVector p S) (r : ℕ)
    (hx : ∀ i : ℕ, i < r → x.coeff i = 0) :
    ∀ i : ℕ, i < r → (x + y).coeff i = y.coeff i := by sorry
