-- Prove2me | Definitions.Def_Couret_MembershipDecisionTree_ec39964080f5
-- name    : Couret_MembershipDecisionTree_ec39964080f5
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:15:36.171977+00:00
-- url     : https://prove2.me/theorems/84c7ecb0-96f4-40d3-90e2-c97cffc53273
-- title:
--   Binary membership decision trees
-- statement:
--   Defines finite binary trees whose internal nodes ask membership of a position and whose leaves return finite supports. Defines execution, maximum query depth, leaf outputs, and correctness on a family. The fixed-tree constructor asks a prescribed sequence of positions and applies a supplied decoder to the full Boolean answer vector; depth zero is allowed.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/MembershipDecisionTree.lean; source file SHA-256 5e2fd5ee9c8bf68b4cdf22b33c6271447fa8b254d46cd000dc67939ef57a2581

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

/-- Finite deterministic adaptive protocols using only labelled membership queries. -/
inductive MembershipTree (α : Type*) where
  | leaf (output : Finset α)
  | query (position : α) (no yes : MembershipTree α)

namespace MembershipTree

def depth {α : Type*} : MembershipTree α → ℕ
  | leaf _ => 0
  | query _ no yes => max no.depth yes.depth+1

def run {α : Type*} [DecidableEq α] (tree : MembershipTree α) (truth : Finset α) : Finset α :=
  match tree with
  | leaf output => output
  | query x no yes => if x ∈ truth then yes.run truth else no.run truth

def leaves {α : Type*} [DecidableEq α] : MembershipTree α → Finset (Finset α)
  | leaf output => {output}
  | query _ no yes => no.leaves ∪ yes.leaves

def CorrectOn {α : Type*} [DecidableEq α] (tree : MembershipTree α) (P : Set (Finset α)) : Prop :=
  ∀ T ∈ P, tree.run T=T









/-- A full tree implementing a nonadaptive query list and its decoder. -/
def fixed {α : Type*} : (d : ℕ) → (Fin d → α) → ((Fin d → Bool) → Finset α) → MembershipTree α
  | 0,_,decode => leaf (decode Fin.elim0)
  | d+1,q,decode => query (q 0)
      (fixed d (fun i => q i.succ) (fun b => decode (Fin.cons false b)))
      (fixed d (fun i => q i.succ) (fun b => decode (Fin.cons true b)))





end MembershipTree
end Couret.InterIA.Fibres


