-- Prove2me | Theorems.Thm_Couret_InterIA_QuotientBridge_normal_quotient_period
-- name    : Couret.InterIA.QuotientBridge.normal_quotient_period
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:04.840193+00:00
-- url     : https://prove2.me/theorems/a833eae4-04e2-45f1-b82e-2d6e6c96b8dc
-- title:
--   normal quotient period
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. For every positive natural m and finite S,T⊆ℤ/(2m)ℤ, assume |S∩T|=2, there exist a₀,b₀ with S∖T={a₀,a₀+m} and T∖S={b₀,b₀+m}, and Q(S,z)=Q(T,z) for every z. Then there exist a,b∈ℤ/(2m)ℤ such that S∖T={a,a+m}, T∖S={b,b+m}, and the additive order of the reduction of b−a modulo m is 2 or 4.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientBridge.lean, lines 152–201; source file SHA-256 e3039f9ffa13d11690462eb5cb4b77969858bb42cad9a16ac2921936d5203630; theorem Couret.InterIA.QuotientBridge.normal_quotient_period

import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_QuotientBridge_pp_quotient_invariant
import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
open Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo Couret.InterIA.Projection











section Moment
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







end Moment

theorem normal_quotient_period (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m)))
    (hN : Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S T)
    (hsq : ∀ z, orderedSquare S z = orderedSquare T z) :
    ∃ a b : ZMod (2*m), S \ T = fibre (m : ZMod (2*m)) a ∧
      T \ S = fibre (m : ZMod (2*m)) b ∧
      (addOrderOf (projection m (b-a))=2 ∨ addOrderOf (projection m (b-a))=4) := by sorry




end Couret.InterIA.QuotientBridge
