-- Prove2me | Definitions.Def_Couret_QuotientOrbits_0c82b3d4a090
-- name    : Couret_QuotientOrbits_0c82b3d4a090
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:07:27.251029+00:00
-- url     : https://prove2.me/theorems/89795905-0b4a-499b-a3bc-30501347c34e
-- title:
--   Four-atom group-ring supports
-- statement:
--   For $a,b,c,d$ in an abelian group, the four-atom expression is $$X^a+X^b+X^c+X^d\in\mathbb Z[G].$$ Repeated entries retain multiplicity. The associated coefficient lemmas support translation-orbit and quotient arguments for these four-term expressions.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientOrbits.lean; source file SHA-256 90a9fb6b3c18f1724e125dbed131f8a89171589bc356f33f17aa73d3bf1014b8

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
import Definitions.Def_Couret_QuotientPeriods_cf8d74422994

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def atoms (a b c d : G) : AddMonoidAlgebra ℤ G :=
  AddMonoidAlgebra.single a 1+AddMonoidAlgebra.single b 1+
    AddMonoidAlgebra.single c 1+AddMonoidAlgebra.single d 1

theorem invariant_coeff_shift (W : AddMonoidAlgebra ℤ G) (δ : G)
    (he : W=AddMonoidAlgebra.single δ 1*W) (x : G) :
    W.coeff (x+δ)=W.coeff x := by
  have h := congrArg (fun f : AddMonoidAlgebra ℤ G => f.coeff (x+δ)) he
  change W.coeff (x+δ)=(AddMonoidAlgebra.single δ 1*W).coeff (x+δ) at h
  rw [Couret.InterIA.GroupRing.monomial_translate_coefficient] at h
  simpa using h



theorem atoms_coeff_nonzero (a b c d x : G) :
    (atoms a b c d).coeff x ≠ 0 ↔ x=a ∨ x=b ∨ x=c ∨ x=d := by
  change ((AddMonoidAlgebra.single a (1 : ℤ) : AddMonoidAlgebra ℤ G) x+
    (AddMonoidAlgebra.single b (1 : ℤ) : AddMonoidAlgebra ℤ G) x+
    (AddMonoidAlgebra.single c (1 : ℤ) : AddMonoidAlgebra ℤ G) x+
    (AddMonoidAlgebra.single d (1 : ℤ) : AddMonoidAlgebra ℤ G) x) ≠ 0 ↔ _
  simp only [AddMonoidAlgebra.single_apply]
  split_ifs <;> simp_all [eq_comm]

theorem atoms_translation_closed (a b c d δ : G)
    (he : atoms a b c d=AddMonoidAlgebra.single δ 1*atoms a b c d)
    (x : G) (hx : x=a ∨ x=b ∨ x=c ∨ x=d) :
    x+δ=a ∨ x+δ=b ∨ x+δ=c ∨ x+δ=d := by
  apply (atoms_coeff_nonzero a b c d (x+δ)).mp
  rw [invariant_coeff_shift _ δ he]
  exact (atoms_coeff_nonzero a b c d x).mpr hx

end Couret.InterIA.Catalogue.Orbits


