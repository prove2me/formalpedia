-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_double_fibre_eq_translate
-- name    : Couret.STROBO2TORS.recoh_double_fibre_eq_translate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:08.936312+00:00
-- url     : https://prove2.me/theorems/1cfd5665-af05-4f2c-9e00-37be7af5f1a7
-- title:
--   A nonempty doubling fibre is a translate of the kernel
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $t,\sigma\in G$ and $2\sigma=t$, then
--
--   $$\{x:2x=t\}=\{u:2u=0\}+\sigma.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohDecoderBounds.lean, lines 33–52; source file SHA-256 007136596acc888d04aeee8638a09fb1002302843da3cdae7d6c320ef17978d6; theorem Couret.STROBO2TORS.recoh_double_fibre_eq_translate

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

theorem recoh_double_fibre_eq_translate (t sigma : G)
    (hsigma : sigma + sigma = t) :
    recohDoubleFibre t = translateSupport (recohDoubleFibre (0 : G)) sigma := by sorry
























end Couret.STROBO2TORS
