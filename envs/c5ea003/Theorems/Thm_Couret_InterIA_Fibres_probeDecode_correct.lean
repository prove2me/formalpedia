-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_probeDecode_correct
-- name    : Couret.InterIA.Fibres.probeDecode_correct
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:07.396116+00:00
-- url     : https://prove2.me/theorems/9e5505ac-3b86-44f8-a990-70e70cc3bc22
-- title:
--   A separating membership decoder recovers each candidate
-- statement:
--   Let $P$ be a family of finite subsets, $q_1,\ldots,q_d$ membership probes separating members of $P$, and $F$ any fallback finite set. The decoder chooses a member of $P$ matching an answer vector if one exists, otherwise $F$. For every $T\in P$,
--
--   $$\operatorname{decode}_{P,q,F}(([q_i\in T])_{i=1}^d)=T.$$
--
--   This certifies decoding from separating probes, independently of the fallback.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/FixedMembershipProbes.lean, lines 180–188; source file SHA-256 ad66985fbc01dce4c10be3faf60eae345c3ccda9af3d563dfd2ae2e57262cb82; theorem Couret.InterIA.Fibres.probeDecode_correct

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

theorem probeDecode_correct {α : Type*} [DecidableEq α] {d : ℕ}
    (P : Set (Finset α)) (q : Fin d → α) (fallback : Finset α) (hq : ProbeSeparates P q)
    (T : Finset α) (hT : T ∈ P) : probeDecode P q fallback (probeAnswers q T)=T := by sorry




end Couret.InterIA.Fibres
