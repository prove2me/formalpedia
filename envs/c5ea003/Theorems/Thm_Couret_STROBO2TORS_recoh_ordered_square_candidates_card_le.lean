-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_ordered_square_candidates_card_le
-- name    : Couret.STROBO2TORS.recoh_ordered_square_candidates_card_le
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:55:36.606125+00:00
-- url     : https://prove2.me/theorems/e4ddb223-240d-4c43-907b-77f4885c305b
-- title:
--   Candidate count is at most twenty times two-torsion
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Assume $G$ finite. For every three-element support $S$, $$|\operatorname{Candidates}(Q_S)|\le20|H|.$$
--
--   This bounds the unrefined ordered-square candidate decoder.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohDecoderBounds.lean, lines 158–164; source file SHA-256 007136596acc888d04aeee8638a09fb1002302843da3cdae7d6c320ef17978d6; theorem Couret.STROBO2TORS.recoh_ordered_square_candidates_card_le

import Aesop
import Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_double_fibre_eq_translate
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_support_card_le_six
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

theorem recoh_ordered_square_candidates_card_le (S : Finset G)
    (hS : S.card = 3) :
    (recohCandidates (orderedSquare S)).card ≤
      20 * Nat.card (recohTorsionSubgroup (G := G) 2) := by sorry


end Couret.STROBO2TORS
