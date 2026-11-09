-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_xor_family_four_probes
-- name    : Couret.InterIA.Fibres.xor_family_four_probes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:06:03.746349+00:00
-- url     : https://prove2.me/theorems/a4fb5a53-090f-4c61-b152-b3ba64fbcd3b
-- title:
--   Two membership probes separate a four-member xor family
-- statement:
--   Let $\alpha$ have decidable equality and $P$ be a family of exactly four finite subsets closed under ternary symmetric difference. Then two positions $q_0,q_1\in\alpha$ distinguish its members: $$T\mapsto(1_{q_0\in T},1_{q_1\in T})\text{ is injective on }P.$$
--
--   This is a fixed, nonadaptive bank.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/FixedMembershipProbes.lean, lines 76–126; source file SHA-256 ad66985fbc01dce4c10be3faf60eae345c3ccda9af3d563dfd2ae2e57262cb82; theorem Couret.InterIA.Fibres.xor_family_four_probes

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
import Theorems.Thm_Couret_InterIA_Fibres_xor_four_coordinate_separates
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem xor_family_four_probes {α : Type*} [DecidableEq α]
    (P : Set (Finset α)) (hc : P.ncard=4) (hxor : XorClosed P) :
    ∃ q : Fin 2 → α, ProbeSeparates P q := by sorry
















end Couret.InterIA.Fibres
