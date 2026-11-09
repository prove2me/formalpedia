-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_candidates_card_le_twenty
-- name    : Couret.STROBO2TORS.recoh_prepared_fast_candidates_card_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:27:05.240577+00:00
-- url     : https://prove2.me/theorems/cb52ccb3-8a22-4fb7-bbab-26507d8112b5
-- title:
--   Prepared fast candidates have at most twenty members
-- statement:
--   Let $G$ be an abelian group. For a finite set $U\subseteq G$, a partial halving function $h:G\to G\cup\{\mathrm{none}\}$ and a recovery map $f$, fast candidates are $f(\{\sigma-e:e\in E\})$ for three-subsets $E\subseteq U$ on which $h(\sum E)=\sigma$ is defined. The prepared generator additionally applies any Boolean precheck to edge representatives before recovery. If $|U|\le6$, then
--
--   $$|\operatorname{PreparedFastCandidates}(U,h,f,\mathrm{precheck})|\le20.$$
--
--   The bound needs no semantic specification of the supplied functions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPreparedDecoder.lean, lines 70–75; source file SHA-256 f6373eabc2c71ec81235339b571dd8d279e57b6848a6d8ac04fcaaf979efd104; theorem Couret.STROBO2TORS.recoh_prepared_fast_candidates_card_le_twenty

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_edge_sets_card_le_twenty
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

theorem recoh_prepared_fast_candidates_card_le_twenty
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (precheck : Finset G → Bool) (hU : U.card ≤ 6) :
    (recohPreparedFastCandidates U half recover precheck).card ≤ 20 := by sorry








variable {J : Type*}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable {I : Type*} [Fintype I]







end Couret.STROBO2TORS
