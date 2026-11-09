-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_singleton_step_preserved
-- name    : Couret.CayleyDoublet.singleton_step_preserved
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:58.858992+00:00
-- url     : https://prove2.me/theorems/3455cece-0e7b-45ad-b150-a33414abdc81
-- title:
--   Every isomorphism preserves the intrinsic singleton step
-- statement:
--   Let $G$ be an abelian group. Let $a,b,c,h\in G$, with $h\ne0$, $2h=0$, $a\notin\{b,b+h,c,c+h\}$, and $3(a-c)\in\{0,h\}$. Let $f:G\to G$ be a bijection carrying the directed Cayley relation of $\{a,b,b+h\}$ to that of $\{a,c,c+h\}$. For every $x\in G$,
--
--   $$f(x+a)=f(x)+a.$$
--
--   This identifies a translation preserved even by a vertex bijection that was not assumed additive.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourFamily.lean#L21-L59, lines 21–59; source file SHA-256 69673503e6f3aca79e315886c18f61d28f50b63808dcab10fe39ca827bd7c5f3; theorem Couret.CayleyDoublet.singleton_step_preserved

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_isMate
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_unique_of_order_three
import Theorems.Thm_Couret_CayleyDoublet_singletonArc_iff
import Theorems.Thm_Couret_CayleyDoublet_singletonArc_iff_point
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

theorem singleton_step_preserved
    (a b c h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hab : a ≠ b) (habh : a ≠ b + h)
    (hac : a ≠ c) (hach : a ≠ c + h)
    (hthreeT : (a - c) + (a - c) + (a - c) = 0 ∨
      (a - c) + (a - c) + (a - c) = h)
    (f : G ≃ G)
    (hf : ∀ x y, CayleyArc (TripleSupport a b h) x y ↔
      CayleyArc (TripleSupport a c h) (f x) (f y))
    (x : G) :
    f (x + a) = f x + a := by sorry





end TwoColourObstruction

end Couret.CayleyDoublet
