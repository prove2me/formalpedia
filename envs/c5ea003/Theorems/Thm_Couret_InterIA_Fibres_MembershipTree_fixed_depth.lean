-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_MembershipTree_fixed_depth
-- name    : Couret.InterIA.Fibres.MembershipTree.fixed_depth
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:22.878234+00:00
-- url     : https://prove2.me/theorems/8e881d0e-d5b6-4279-b12f-69c600b19eb2
-- title:
--   A fixed membership questionnaire has its prescribed depth
-- statement:
--   Let $A$ be a type, $d\in\mathbb N$, $q:\{0,\ldots,d-1\}\to A$ query positions, and $D:\{0,1\}^d\to\operatorname{Finset}(A)$ a decoder. Form the binary membership tree that asks the positions in order and returns $D$ of the answers. Then
--
--   $$\operatorname{depth}(\operatorname{fixed}(d,q,D))=d.$$
--
--   Repeated query positions and the boundary case $d=0$ are allowed.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/MembershipDecisionTree.lean, lines 82–86; source file SHA-256 5e2fd5ee9c8bf68b4cdf22b33c6271447fa8b254d46cd000dc67939ef57a2581; theorem Couret.InterIA.Fibres.MembershipTree.fixed_depth

import Definitions.Def_Couret_MembershipDecisionTree_ec39964080f5
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
import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset



namespace MembershipTree

theorem fixed_depth {α : Type*} (d : ℕ) (q : Fin d → α) (decode : (Fin d → Bool) → Finset α) :
    (fixed d q decode).depth=d := by sorry




end MembershipTree
end Couret.InterIA.Fibres
