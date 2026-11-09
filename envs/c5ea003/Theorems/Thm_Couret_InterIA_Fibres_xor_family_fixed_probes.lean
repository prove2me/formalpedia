-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_xor_family_fixed_probes
-- name    : Couret.InterIA.Fibres.xor_family_fixed_probes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:49.941208+00:00
-- url     : https://prove2.me/theorems/6c2328df-c10c-4d19-9f2c-4d721f7fa6a7
-- title:
--   Two fixed membership probes suffice for a small xor-closed family
-- statement:
--   Let $P$ be a family of finite subsets of a type $A$, of size one, two, or four. Assume $A_1\triangle A_2\triangle A_3\in P$ whenever $A_1,A_2,A_3\in P$. Then there are $d\le2$ and fixed query positions $q_0,\ldots,q_{d-1}\in A$ such that
--
--   $$|P|=2^d,\qquad T,U\in P,\ [\forall i<d,\ q_i\in T\iff q_i\in U]\Longrightarrow T=U.$$
--
--   This is a nonadaptive membership identification theorem.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/FixedMembershipProbes.lean, lines 128–150; source file SHA-256 ad66985fbc01dce4c10be3faf60eae345c3ccda9af3d563dfd2ae2e57262cb82; theorem Couret.InterIA.Fibres.xor_family_fixed_probes

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
import Theorems.Thm_Couret_InterIA_Fibres_xor_family_four_probes
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem xor_family_fixed_probes {α : Type*} [DecidableEq α]
    (P : Set (Finset α)) (hc : P.ncard=1 ∨ P.ncard=2 ∨ P.ncard=4) (hxor : XorClosed P) :
    ∃ d : ℕ, d ≤ 2 ∧ P.ncard=2^d ∧ ∃ q : Fin d → α, ProbeSeparates P q := by sorry














end Couret.InterIA.Fibres
