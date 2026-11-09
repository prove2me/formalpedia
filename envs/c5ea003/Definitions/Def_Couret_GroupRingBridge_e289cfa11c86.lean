-- Prove2me | Definitions.Def_Couret_GroupRingBridge_e289cfa11c86
-- name    : Couret_GroupRingBridge_e289cfa11c86
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:26.752205+00:00
-- url     : https://prove2.me/theorems/16fddc04-7bd5-4c85-8fca-eec7b35a5b9a
-- title:
--   Finite support indicators in the integer group ring
-- statement:
--   A finite support $S$ in an abelian group is represented in $\mathbb Z[G]$ by
--
--   $$1_S=\sum_{a\in S}[a].$$
--
--   The bundle relates coefficients of products and squares to pair-sum counts, translation to multiplication by a monomial, and half-turn monomials to involutions. It also supplies cancellation facts for integer coefficients. This provides the group-ring language used in support-collision arguments.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/GroupRingBridge.lean; source file SHA-256 93ff5e598eb6a676328a31e8492480c37a2b6ad19927c33980aaf4eabe01656d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_TwoPointCollision_eefa36a5b454
import Mathlib.Algebra.MonoidAlgebra.Defs

set_option autoImplicit false
namespace Couret.InterIA.GroupRing
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The integral indicator, in the additive group ring. -/
noncomputable def indicator (S : Finset G) : AddMonoidAlgebra ℤ G :=
  ∑ a ∈ S, AddMonoidAlgebra.single a 1

theorem indicator_apply (S : Finset G) (z : G) :
    (indicator S).coeff z = if z ∈ S then 1 else 0 := by
  simp only [indicator, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  change (∑ a ∈ S, (AddMonoidAlgebra.single a (1 : ℤ) : AddMonoidAlgebra ℤ G) z) = _
  simp [AddMonoidAlgebra.single_apply, eq_comm]

theorem indicator_mul_coefficient (S T : Finset G) (z : G) :
    (indicator S * indicator T).coeff z =
      ∑ a ∈ S, ∑ b ∈ T, (if a+b=z then 1 else 0 : ℤ) := by
  unfold indicator
  simp only [Finset.sum_mul, Finset.mul_sum, AddMonoidAlgebra.single_mul_single,
    one_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact AddMonoidAlgebra.single_apply

theorem indicator_square_coefficient (S : Finset G) (z : G) :
    (indicator S * indicator S).coeff z = (orderedSquare S z : ℤ) := by
  rw [indicator_mul_coefficient]
  simp [orderedSquare, Nat.cast_sum, apply_ite]

theorem square_equality_iff (S T : Finset G) :
    indicator S * indicator S = indicator T * indicator T ↔
      ∀ z, orderedSquare S z = orderedSquare T z := by
  constructor
  · intro he z
    have hc := congrArg (fun f : AddMonoidAlgebra ℤ G => f.coeff z) he
    change (indicator S * indicator S).coeff z = (indicator T * indicator T).coeff z at hc
    rw [indicator_square_coefficient, indicator_square_coefficient] at hc
    exact_mod_cast hc
  · intro he
    apply AddMonoidAlgebra.ext
    intro z
    change (indicator S * indicator S).coeff z = (indicator T * indicator T).coeff z
    rw [indicator_square_coefficient, indicator_square_coefficient, he z]

theorem monomial_translate_coefficient (h : G) (f : AddMonoidAlgebra ℤ G) (z : G) :
    ((AddMonoidAlgebra.single h (1 : ℤ) : AddMonoidAlgebra ℤ G) * f).coeff z = f.coeff (z-h) := by
  change ((AddMonoidAlgebra.single h (1 : ℤ) : AddMonoidAlgebra ℤ G) * f) z = f (z-h)
  rw [AddMonoidAlgebra.single_mul_apply, one_mul]
  congr 1
  abel

theorem indicator_translate (S : Finset G) (h : G) :
    indicator (S.image (fun x => x+h)) =
      AddMonoidAlgebra.single h 1 * indicator S := by
  unfold indicator
  rw [Finset.sum_image (fun a _ b _ he => add_right_cancel he), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp [AddMonoidAlgebra.single_mul_single, add_comm]

theorem antipodal_monomial_square (h : G) (hh2 : h+h=0) :
    (AddMonoidAlgebra.single h (1 : ℤ) : AddMonoidAlgebra ℤ G) *
      AddMonoidAlgebra.single h 1 = 1 := by
  simp [AddMonoidAlgebra.single_mul_single, hh2, AddMonoidAlgebra.one_def]

theorem integer_coefficient_no_two_torsion (f : AddMonoidAlgebra ℤ G)
    (hf : (2 : AddMonoidAlgebra ℤ G)*f=0) : f=0 := by
  ext z
  have he : f+f=0 := by simpa [two_mul] using hf
  have hz := congrArg (fun g : AddMonoidAlgebra ℤ G => g z) he
  change f z+f z=0 at hz
  change f z=0
  omega

end Couret.InterIA.GroupRing


