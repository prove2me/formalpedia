-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_decoder_card_le_twenty
-- name    : Couret.STROBO2TORS.recoh_prepared_fast_decoder_card_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:37.386416+00:00
-- url     : https://prove2.me/theorems/5ef7ce17-6fa6-46aa-9ccb-fd3ea1032251
-- title:
--   Any prepared fast decoder has at most twenty outputs from six positions
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $R_S$ the ordered pair-sum count of a finite support, and $P_\chi(S)=\sum_{s\in S}\chi(s)$. Let $U\subseteq G$ with $|U|\le6$, and let $h:G\to\operatorname{Option}(G)$, $r:\operatorname{Finset}(G)\to\operatorname{Finset}(G)$, and Boolean support predicates $b,c$ be arbitrary. The specified prepared fast decoder first prechecks candidate representatives, applies $r$, and then applies $c$. It satisfies
--
--   $$|\operatorname{PreparedFast}(U,h,r,b,c)|\le20.$$
--
--   The count is independent of the correctness of those supplied functions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPreparedDecoder.lean, lines 77–82; source file SHA-256 f6373eabc2c71ec81235339b571dd8d279e57b6848a6d8ac04fcaaf979efd104; theorem Couret.STROBO2TORS.recoh_prepared_fast_decoder_card_le_twenty

import Aesop
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_candidates_card_le_twenty
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8

set_option autoImplicit false

/-!
Move the square test before sign recovery, as in Python `_prepare_square`.

The generic prepared decoder filters the chosen representatives before
recovery and retains the complete final checker after recovery.  The two
orders give the same answer whenever a final acceptance implies acceptance
of the representative by the precheck.  For the square test, this implication
follows from invariance under every two-torsion translation, for all finite
supports.  The resulting coefficient backend is therefore equal to the
previously certified backend, under the same support-coverage contract.

This module certifies an order of mathematical operations.  It does not
certify the separate Python cache, parser, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_prepared_fast_decoder_card_le_twenty
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (precheck check : Finset G → Bool) (hU : U.card ≤ 6) :
    (recohPreparedFastDecoder U half recover precheck check).card ≤ 20 := by sorry






variable {J : Type*}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable {I : Type*} [Fintype I]







end Couret.STROBO2TORS
