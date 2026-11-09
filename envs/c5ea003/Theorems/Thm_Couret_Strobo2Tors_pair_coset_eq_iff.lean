-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_pair_coset_eq_iff
-- name    : Couret.Strobo2Tors.pair_coset_eq_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:30:51.349817+00:00
-- url     : https://prove2.me/theorems/49986239-70ac-403a-a112-b18deebbe8ec
-- title:
--   Equality of two-point cosets
-- statement:
--   Let G be an abelian group and x,y,u in G with 2u=0, allowing u=0. Then $$\{x,x+u\}=\{y,y+u\}\iff y=x\text{ or }y=x+u.$$ The finite sets can be singletons. The source section declares a finite ambient group; CI determines whether this unused declaration survives elaboration.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/Rectangle.lean#L13-L30, lines 13–30; source file SHA-256 970727a249cdc2c537ec995230f642206b1cddba759bb4b266d9187410147ede; theorem Couret.Strobo2Tors.pair_coset_eq_iff

import Definitions.Def_Couret_Prelude_5b3cc8c481fb
import Mathlib
import Definitions.Def_Couret_Prelude_5b3cc8c481fb

/-!
First local rectangle rigidity lemma: equality of two-point cosets of
an order-two subgroup. This is only one ingredient of the type-II argument.
No general STROBO classification is claimed.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem pair_coset_eq_iff (x y u : G) (hu : u + u = 0) :
    ({x, x + u} : Finset G) = {y, y + u} ↔
      y = x ∨ y = x + u := by sorry


end Couret.Strobo2Tors
