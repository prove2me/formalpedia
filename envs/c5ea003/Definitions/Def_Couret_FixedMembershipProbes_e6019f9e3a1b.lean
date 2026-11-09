-- Prove2me | Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b
-- name    : Couret_FixedMembershipProbes_e6019f9e3a1b
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:14:22.736221+00:00
-- url     : https://prove2.me/theorems/0c3ca1df-76bd-43ba-9beb-a2d159b337af
-- title:
--   Fixed membership probes and answer decoding
-- statement:
--   Defines a list of fixed positions to separate a family when equal membership answers force equal sets. Defines the Boolean answer vector of a finite support and a choice-based decoder selecting a family member with that vector, or returning a supplied fallback if none exists. No effective search or finiteness of the entire ambient type is asserted.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/FixedMembershipProbes.lean; source file SHA-256 ad66985fbc01dce4c10be3faf60eae345c3ccda9af3d563dfd2ae2e57262cb82

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

/-- A fixed list of labelled positions separates every pair of candidates. -/
def ProbeSeparates {α : Type*} [DecidableEq α] {d : ℕ}
    (P : Set (Finset α)) (q : Fin d → α) : Prop :=
  ∀ T ∈ P, ∀ U ∈ P, (∀ i, q i ∈ T ↔ q i ∈ U) → T=U















def probeAnswers {α : Type*} [DecidableEq α] {d : ℕ} (q : Fin d → α) (T : Finset α) : Fin d → Bool :=
  fun i => decide (q i ∈ T)





noncomputable def probeDecode {α : Type*} [DecidableEq α] {d : ℕ}
    (P : Set (Finset α)) (q : Fin d → α) (fallback : Finset α) (b : Fin d → Bool) : Finset α :=
  by
    classical
    exact if h : ∃ T ∈ P, probeAnswers q T=b then Classical.choose h else fallback





end Couret.InterIA.Fibres


