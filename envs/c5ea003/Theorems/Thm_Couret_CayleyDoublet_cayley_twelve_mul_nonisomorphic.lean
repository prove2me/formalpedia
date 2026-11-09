-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_cayley_twelve_mul_nonisomorphic
-- name    : Couret.CayleyDoublet.cayley_twelve_mul_nonisomorphic
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:50:21.29965+00:00
-- url     : https://prove2.me/theorems/42e4c3f5-3ae2-4e53-8534-fc7440084564
-- title:
--   Explicit nonisomorphic directed Cayley triples at every positive scale
-- statement:
--   For a natural r>0, put G=Z/(12r), S={1,1+2r,1+8r} and T={1,1+4r,1+10r}, all entries taken modulo 12r. No bijection f:G→G can satisfy $$[y-x\in S]\iff[f(y)-f(x)\in T]\quad(x,y\in G).$$ Thus these directed Cayley graphs are nonisomorphic under arbitrary vertex bijections, not only affine maps.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourZMod.lean#L28-L142, lines 28–142; source file SHA-256 b9c53a814edc6573ecdb61d909b0988ad5b0154cde1bee9fcb4d39181b7464f1; theorem Couret.CayleyDoublet.cayley_twelve_mul_nonisomorphic

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_noIso_of_two_colours
import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1

set_option autoImplicit false

/-!
CAYLEY-TWO-COLOUR-ZMOD — arithmetic specialization, 2026-10-14.

This candidate closes the concrete modular arithmetic premises of the
already compiled, conditional noIso_of_two_colours theorem.

Status: NEW CANDIDATE. Do not report as compiled without the
cayley-two-colour-family-lean workflow passing on its exact commit SHA.
Only directed graph nonisomorphism is intended; no academic priority.
-/

namespace Couret.CayleyDoublet

theorem cayley_twelve_mul_nonisomorphic
    (r : ℕ) (hr : 0 < r)
    (f : ZMod (12 * r) ≃ ZMod (12 * r))
    (hf : ∀ x y : ZMod (12 * r),
      CayleyArc (TripleSupport (1 : ZMod (12 * r))
        ((1 + 2 * r : ℕ) : ZMod (12 * r))
        ((6 * r : ℕ) : ZMod (12 * r))) x y ↔
      CayleyArc (TripleSupport (1 : ZMod (12 * r))
        ((1 + 4 * r : ℕ) : ZMod (12 * r))
        ((6 * r : ℕ) : ZMod (12 * r))) (f x) (f y)) :
    False := by sorry



end Couret.CayleyDoublet
