-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_xor_four_coordinate_separates
-- name    : Couret.InterIA.Fibres.xor_four_coordinate_separates
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:53.468071+00:00
-- url     : https://prove2.me/theorems/f74c4d05-09e3-4306-928c-52b3650e36b2
-- title:
--   Two coordinates separate a four-member XOR family
-- statement:
--   Let $A,B,C$ be finite subsets, and let $x,y$ be elements. Suppose $x$ has different membership in $A,B$ but identical membership in $A,C$, while $y$ has different membership in $A,C$. Set $D=A\mathbin\triangle B\mathbin\triangle C$. Then
--
--   $$T\longmapsto([x\in T],[y\in T])\text{ is injective on }\{A,B,C,D\}.$$
--
--   This supplies two probes for a binary affine plane of finite sets.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/FixedMembershipProbes.lean, lines 39–74; source file SHA-256 ad66985fbc01dce4c10be3faf60eae345c3ccda9af3d563dfd2ae2e57262cb82; theorem Couret.InterIA.Fibres.xor_four_coordinate_separates

import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem xor_four_coordinate_separates {α : Type*} [DecidableEq α]
    (A B C : Finset α) (x y : α)
    (hx : ¬ (x ∈ A ↔ x ∈ B)) (hc : x ∈ A ↔ x ∈ C)
    (hy : ¬ (y ∈ A ↔ y ∈ C)) :
    ProbeSeparates ({A,B,C,symmDiff (symmDiff A B) C} : Set (Finset α))
      (fun i : Fin 2 => if i=0 then x else y) := by sorry


















end Couret.InterIA.Fibres
