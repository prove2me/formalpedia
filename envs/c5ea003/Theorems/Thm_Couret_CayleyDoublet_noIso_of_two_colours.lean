-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_noIso_of_two_colours
-- name    : Couret.CayleyDoublet.noIso_of_two_colours
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:32:33.161395+00:00
-- url     : https://prove2.me/theorems/862609d8-5ba8-4c74-b701-705406b4a20f
-- title:
--   An integral step relation obstructs two-colour isomorphism
-- statement:
--   Let $G$ be an abelian group. Let $a,b,c,h\in G$, with $h\ne0$, $2h=0$, $a\notin\{b,b+h,c,c+h\}$, and $3(a-c)\in\{0,h\}$. Let $f:G\to G$ be a bijection carrying the directed Cayley relation of $\{a,b,b+h\}$ to that of $\{a,c,c+h\}$. If $k\in\mathbb N$, $b=ka$, and $b\notin\{c,c+h\}$, these hypotheses are inconsistent:
--
--   $$\bot.$$
--
--   Thus no such directed graph isomorphism exists, including the case $k=0$ whenever the remaining hypotheses hold.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourFamily.lean#L61-L129, lines 61–129; source file SHA-256 69673503e6f3aca79e315886c18f61d28f50b63808dcab10fe39ca827bd7c5f3; theorem Couret.CayleyDoublet.noIso_of_two_colours

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_doubletArc_iff
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_isMate
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_unique_of_order_three
import Theorems.Thm_Couret_CayleyDoublet_markedArc_iff_pair
import Theorems.Thm_Couret_CayleyDoublet_singleton_step_preserved
import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1

set_option autoImplicit false

/-!
CAYLEY-TWO-COLOUR-FAMILY (14 October 2026).

A directed-graph obstruction derived from *both* intrinsic arc colours.
The universal algebraic theorem is independent of cyclic labels. The
specific ZMod arithmetic is kept in a separate section below. This is an
internal Lean candidate pending a matching-SHA CI compilation.
No academic originality, publication or external review claim.
-/

namespace Couret.CayleyDoublet

section TwoColourObstruction

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem noIso_of_two_colours
    (a b c h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hab : a ≠ b) (habh : a ≠ b + h)
    (hac : a ≠ c) (hach : a ≠ c + h)
    (hthreeT : (a - c) + (a - c) + (a - c) = 0 ∨
      (a - c) + (a - c) + (a - c) = h)
    (k : ℕ) (hbk : b = k • a)
    (hbc : b ≠ c) (hbch : b ≠ c + h)
    (f : G ≃ G)
    (hf : ∀ x y, CayleyArc (TripleSupport a b h) x y ↔
      CayleyArc (TripleSupport a c h) (f x) (f y)) : False := by sorry



end TwoColourObstruction

end Couret.CayleyDoublet
