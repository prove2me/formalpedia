-- Prove2me | Definitions.Def_Hirsch_additive_portal_repair
-- name    : Hirsch_additive_portal_repair
-- status  : Definition
-- author  : @jjosh
-- created : 2026-09-12T23:39:28.461481+00:00
-- url     : https://prove2.me/theorems/be8f4ff8-23bd-4894-a523-ab6271d326f0
-- title:
--   Finite additive-spill repair certificates with actual leaf routes
-- statement:
--   A finite additive repair certificate assembles actual steps of a relation R.
--   A leaf has excess e<=b and an actual route of cost<=C*e. A nonleaf records one
--   initial R-edge or stationary step, followed by child repairs. Child dimensions
--   strictly drop, each child excess is at most the parent e, and sibling excesses
--   sum to at most e+b. Internal parents have positive dimension and e>b.
--   The tags must be separately justified when used for polytope geometry.
-- source:
--   Explicit conditional recurrence and actual-route assembly; https://github.com/jjoshua2/prove2me-work/tree/b7a832e9ff98743d53c66d6e471fd0828891d22d

import Mathlib
open scoped BigOperators
namespace HirschRegionRoute
def Route {V : Type*} (R : V → V → Prop) (B : ℕ) (u v : V) : Prop :=
  ∃ w : ℕ → V, w 0 = u ∧ w B = v ∧
    ∀ j < B, w j = w (j + 1) ∨ R (w j) (w (j + 1))

end HirschRegionRoute
namespace HirschAdditiveAllowance
open HirschRegionRoute
variable {V : Type*}
inductive AdditiveRepair (R : V → V → Prop) (b C : ℕ) :
    V → V → ℕ → ℕ → ℕ → Prop
  | leaf (x y : V) (h e cost : ℕ) (he : e ≤ b)
      (hr : Route R cost x y) (hc : cost ≤ C*e) : AdditiveRepair R b C x y h e cost
  | node (h e n : ℕ) (u : V) (p : ℕ → V)
      (dims mass costs : Fin n → ℕ)
      (he : b < e) (hh : 0 < h) (hfirst : u=p 0 ∨ R u (p 0))
      (hdrop : ∀ i, dims i < h) (hmono : ∀ i, mass i ≤ e)
      (hsum : (∑ i, mass i) ≤ e+b)
      (children : ∀ i, AdditiveRepair R b C (p i.val) (p (i.val+1))
        (dims i) (mass i) (costs i)) :
      AdditiveRepair R b C u (p n) h e (1+∑ i, costs i)

end HirschAdditiveAllowance


