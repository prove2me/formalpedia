-- Prove2me | Theorems.Thm_WittenAdSHolography_hawking_page
-- name    : WittenAdSHolography.hawking_page
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:36:11.170829+00:00
-- url     : https://prove2.me/theorems/c8633ca2-886e-456e-ba4b-8cbfb2cfc383
-- title:
--   Eqs. (3.15)–(3.16): Hawking–Page — $\beta(r_+)$ has a maximum and $I(r_+)<0$ for large $r_+$ ($d=3$)
-- statement:
--   For the Euclidean $\mathrm{AdS}_4$ Schwarzschild black hole ($d=3$, AdS radius $1$) with horizon radius $r_+$, let
--   $$\beta(r_+)=\frac{12\pi r_+}{1+3r_+^2},\qquad I(r_+)=\frac{\pi r_+^2(1-r_+^2)}{1+3r_+^2}$$
--   be the period of Euclidean time (3.15) and the action difference between the black hole and thermal AdS (3.16). Then
--
--   1. $\beta$ attains a maximum over $r_+>0$: there is $r_0>0$ with $\beta(r_+)\le\beta(r_0)$ for all $r_+>0$;
--   2. $I(r_+)<0$ for all sufficiently large $r_+$.
--
--   This is the large-$N$ phase transition of the boundary theory on $S^1\times S^2$ as a function of temperature.
-- source:
--   E. Witten, Anti de Sitter Space and Holography, Adv. Theor. Math. Phys. 2 (1998) 253-291, arXiv:hep-th/9802150v2, https://arxiv.org/abs/hep-th/9802150, pp. 32-33, eqs. (3.15)-(3.16)

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology

theorem WittenAdSHolography.hawking_page (β I : ℝ → ℝ)
    (hβ : ∀ r, β r = 12 * Real.pi * r / (1 + 3 * r ^ 2))
    (hI : ∀ r, I r = Real.pi * r ^ 2 * (1 - r ^ 2) / (1 + 3 * r ^ 2)) :
    (∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → β r ≤ β r₀) ∧
      ∃ R : ℝ, ∀ r : ℝ, R < r → I r < 0 := by sorry
