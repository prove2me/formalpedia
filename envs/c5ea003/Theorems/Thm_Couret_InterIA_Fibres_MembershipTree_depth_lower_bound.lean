-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_MembershipTree_depth_lower_bound
-- name    : Couret.InterIA.Fibres.MembershipTree.depth_lower_bound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:41:14.280145+00:00
-- url     : https://prove2.me/theorems/cec5912f-01e5-4a9b-bba1-451cae0df53d
-- title:
--   A binary membership tree needs logarithmic depth
-- statement:
--   Let $P$ be a family of finite subsets of a type and let a binary membership-query tree correctly reconstruct every member of $P$. If $|P|=2^d$ for $d\in\mathbb N$, then
--
--   $$d\le\operatorname{depth}(\mathrm{tree}).$$
--
--   This is the information lower bound for adaptive membership reconstruction.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/MembershipDecisionTree.lean, lines 66–73; source file SHA-256 5e2fd5ee9c8bf68b4cdf22b33c6271447fa8b254d46cd000dc67939ef57a2581; theorem Couret.InterIA.Fibres.MembershipTree.depth_lower_bound

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

theorem depth_lower_bound {α : Type*} [DecidableEq α]
    (tree : MembershipTree α) (P : Set (Finset α)) (d : ℕ)
    (hcard : P.ncard=2^d) (hc : tree.CorrectOn P) : d ≤ tree.depth := by sorry








end MembershipTree
end Couret.InterIA.Fibres
