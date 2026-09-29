-- Prove2me | Theorems.Thm_ZMod_card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow
-- name    : ZMod.card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/df203524-b433-56ac-b6cd-46dc18eb8f47
-- title:
--   Heisenberg bicharacter ζ^{c(h)} on prodℤ/δᵢ and its dual
-- statement:
--   Let $g, d$ be natural numbers and let $\delta : \mathrm{Fin}\,g \to \mathbb N$ have all entries non-zero, with $\prod_i \delta_i = d$. Let $R$ be a commutative ring, $\zeta \in R^\times$ a unit whose image in $R$ satisfies $\zeta^d = 1$, and assume $1 - \zeta^j$ is a unit of $R$ for every natural number $j$ with $0 < j < d$. Write $H = \prod_i \mathbb Z/\delta_i$ and $H' = \mathrm{Hom}(H, \mathbb Z/d)$ for the additive monoid homomorphisms, and let $a \mapsto a.\mathrm{val}$ be the canonical lift $\mathbb Z/d \to \{0,\dots,d-1\}$. The conclusion is the conjunction of five assertions: (i) $\#H' = \#H$ as natural cardinalities; (ii) for all $h_1, h_2 \in H$ and all $c \in H'$, $\zeta^{(c(h_1+h_2)).\mathrm{val}} = \zeta^{(c h_1).\mathrm{val}}\,\zeta^{(c h_2).\mathrm{val}}$ in $R^\times$; (iii) for all $h \in H$ and all $c_1, c_2 \in H'$, $\zeta^{((c_1+c_2)h).\mathrm{val}} = \zeta^{(c_1 h).\mathrm{val}}\,\zeta^{(c_2 h).\mathrm{val}}$; (iv) for every $h \neq 0$ in $H$ there is $c \in H'$ with $\zeta^{(c h).\mathrm{val}} - 1$ a unit of $R$; (v) for every $c \neq 0$ in $H'$ there is $h \in H$ with $\zeta^{(c h).\mathrm{val}} - 1$ a unit of $R$.
--
--   This is the elementary input on the standard bicharacter $e(h,c) = \zeta^{\widetilde{c(h)}}$ pairing a finite abelian group of type $\delta$ with its $\mathbb Z/d$-dual, in the form needed for Heisenberg groups of type $\delta$: equal cardinalities of the two sides, bimultiplicativity in each variable, and separation of non-zero elements by invertibility of $e(h,c)-1$. It is used in the construction of Schrödinger frames for polarised abelian schemes, by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis) and [`AlgebraicGeometry.PolarisedAbelianScheme.nonempty_schrodingerFrame_comp_of_schrodingerFrame`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.nonempty_schrodingerFrame_comp_of_schrodingerFrame).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem ZMod.card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {R : Type*} [CommRing R] (ζ : Rˣ) (hζ : (ζ : R) ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : R) ^ j)) :
    Nat.card (((i : Fin g) → ZMod (δ i)) →+ ZMod d) = Nat.card ((i : Fin g) → ZMod (δ i)) ∧
    (∀ (h₁ h₂ : (i : Fin g) → ZMod (δ i)) (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
      ζ ^ (c (h₁ + h₂)).val = ζ ^ (c h₁).val * ζ ^ (c h₂).val) ∧
    (∀ (h : (i : Fin g) → ZMod (δ i)) (c₁ c₂ : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
      ζ ^ ((c₁ + c₂) h).val = ζ ^ (c₁ h).val * ζ ^ (c₂ h).val) ∧
    (∀ h : (i : Fin g) → ZMod (δ i), h ≠ 0 → ∃ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, IsUnit ((ζ ^ (c h).val : R) - 1)) ∧
    (∀ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, c ≠ 0 → ∃ h : (i : Fin g) → ZMod (δ i), IsUnit ((ζ ^ (c h).val : R) - 1)) := by sorry
