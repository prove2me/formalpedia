-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_probeAnswers_bijective
-- name    : Couret.InterIA.Fibres.probeAnswers_bijective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:30.113401+00:00
-- url     : https://prove2.me/theorems/1830c56b-ebab-4764-be5f-94706d332f8e
-- title:
--   Optimal binary answers give a bijection
-- statement:
--   Let $\alpha$ have decidable equality, $P$ be a family of finite subsets, and $q$ a list of $d\ge0$ positions. If $P$ has finite cardinality $2^d$ and its membership answers at $q$ separate its members, then $$P\longrightarrow\{0,1\}^d$$ given by those answers is bijective. This includes $d=0$.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/FixedMembershipProbes.lean, lines 160–172; source file SHA-256 ad66985fbc01dce4c10be3faf60eae345c3ccda9af3d563dfd2ae2e57262cb82; theorem Couret.InterIA.Fibres.probeAnswers_bijective

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

theorem probeAnswers_bijective {α : Type*} [DecidableEq α] {d : ℕ}
    (P : Set (Finset α)) (q : Fin d → α) (hc : P.ncard=2^d) (hq : ProbeSeparates P q) :
    Function.Bijective (fun T : P => probeAnswers q T.val) := by sorry








end Couret.InterIA.Fibres
