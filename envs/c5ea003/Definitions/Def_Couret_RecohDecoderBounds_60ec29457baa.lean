-- Prove2me | Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
-- name    : Couret_RecohDecoderBounds_60ec29457baa
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:40.047168+00:00
-- url     : https://prove2.me/theorems/bfd9bfc7-316f-4760-afe8-f4594fb86548
-- title:
--   Finite doubling fibres
-- statement:
--   For a finite abelian group and $t\in G$, define
--
--   $$D_t=\{\sigma\in G:2\sigma=t\}.$$
--
--   This finite set records all halves of a group element and supplies the cardinality and translation interface used in decoder bounds.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohDecoderBounds.lean; source file SHA-256 007136596acc888d04aeee8638a09fb1002302843da3cdae7d6c320ef17978d6

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Finite combinatorial bounds for the RECOH candidate decoder.

Each possible three-element edge set E contributes either no half-sum or a
coset of the actual subgroup G[2].  The general counting bound is the number
of edge sets times |G[2]|.  The numerical factor twenty is used only when
the observed square has support of cardinality at most six; this hypothesis
is proved for the ordered square of an actual three-element support.

These are cardinality statements about the finite candidate specification.
They do not by themselves assert a running-time bound for its implementation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The finite fibre of doubling over `t`. -/
def recohDoubleFibre (t : G) : Finset G :=
  Finset.univ.filter (fun sigma => sigma + sigma = t)



























end Couret.STROBO2TORS


