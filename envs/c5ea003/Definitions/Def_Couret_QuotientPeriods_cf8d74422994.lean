-- Prove2me | Definitions.Def_Couret_QuotientPeriods_cf8d74422994
-- name    : Couret_QuotientPeriods_cf8d74422994
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:06:08.803405+00:00
-- url     : https://prove2.me/theorems/ea014e85-42c6-492f-81fe-97f1e370e612
-- title:
--   Moments and periods in the integer group ring
-- statement:
--   For $x$ in an abelian group, the weight map sends $n\in\mathbb Z$ to $nx$. Extending these maps linearly over finitely supported integer coefficients defines the moment
--
--   $$M\!\left(\sum_x a_x[x]\right)=\sum_x a_xx.$$
--
--   The bundle includes its single-atom evaluation and period constraints for four atoms, including the order-dividing-four consequence. This transports equality of group-ring expressions to additive period arithmetic.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientPeriods.lean; source file SHA-256 bd9057bd807a1c77c8c1dc1a052c267cfc2bf47a18692508e9871acc4ea527c8

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Periods
open Finset Couret.InterIA.Catalogue Couret.InterIA.Parity Couret.InterIA.Projection
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Coefficients are integer multiplicities, including possible negative values. -/
noncomputable def weightAt (x : G) : ℤ →+ G where
  toFun n := n • x
  map_zero' := by simp
  map_add' a b := by simp [add_zsmul]

/-- Sum of exponents with their integer multiplicities; no division by the mass. -/
noncomputable def moment : AddMonoidAlgebra ℤ G →+ G :=
  (Finsupp.liftAddHom (fun x : G => weightAt x)).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem moment_single (x : G) (n : ℤ) :
    moment (AddMonoidAlgebra.single x n)=n • x := by
  change (Finsupp.single x n).sum (fun y k => k • y)=n • x
  simp

/-- Translation invariance of four monomials forces four times the shift to vanish. -/
theorem four_atoms_four_nsmul (a b c d δ : G)
    (he : (AddMonoidAlgebra.single a (1 : ℤ) + AddMonoidAlgebra.single b 1+
      AddMonoidAlgebra.single c 1+AddMonoidAlgebra.single d 1) =
      AddMonoidAlgebra.single δ 1 * (AddMonoidAlgebra.single a 1+
        AddMonoidAlgebra.single b 1+AddMonoidAlgebra.single c 1+AddMonoidAlgebra.single d 1)) :
    (4 : ℕ) • δ=0 := by
  have hm := congrArg (moment : AddMonoidAlgebra ℤ G → G) he
  rw [mul_add,mul_add,mul_add] at hm
  simp only [AddMonoidAlgebra.single_mul_single,one_mul,map_add,moment_single,one_zsmul] at hm
  calc
    4 • δ = ((δ+a)+(δ+b)+(δ+c)+(δ+d))-(a+b+c+d) := by abel
    _ = 0 := by rw [← hm]; simp

theorem four_atoms_order_divides_four (a b c d δ : G)
    (he : (AddMonoidAlgebra.single a (1 : ℤ) + AddMonoidAlgebra.single b 1+
      AddMonoidAlgebra.single c 1+AddMonoidAlgebra.single d 1) =
      AddMonoidAlgebra.single δ 1 * (AddMonoidAlgebra.single a 1+
        AddMonoidAlgebra.single b 1+AddMonoidAlgebra.single c 1+AddMonoidAlgebra.single d 1)) :
    addOrderOf δ ∣ 4 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mpr (four_atoms_four_nsmul a b c d δ he)

theorem four_atoms_periods (a b c d δ : G) (hδ : δ ≠ 0)
    (he : (AddMonoidAlgebra.single a (1 : ℤ) + AddMonoidAlgebra.single b 1+
      AddMonoidAlgebra.single c 1+AddMonoidAlgebra.single d 1) =
      AddMonoidAlgebra.single δ 1 * (AddMonoidAlgebra.single a 1+
        AddMonoidAlgebra.single b 1+AddMonoidAlgebra.single c 1+AddMonoidAlgebra.single d 1)) :
    addOrderOf δ=2 ∨ addOrderOf δ=4 := by
  have hd := four_atoms_order_divides_four a b c d δ he
  have hb : addOrderOf δ ≤ 4 := Nat.le_of_dvd (by decide : 0 < 4) hd
  have h0 : addOrderOf δ ≠ 0 := by intro hz; simpa [hz] using hd
  have h1 : addOrderOf δ ≠ 1 := fun h => hδ (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have h3 : addOrderOf δ ≠ 3 := by
    intro hz
    have hf : 3 ∣ 4 := by simpa only [hz] using hd
    norm_num at hf
  omega







end Couret.InterIA.Catalogue.Periods


