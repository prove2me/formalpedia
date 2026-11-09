-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_feasible_edge_sets_card_le_twenty
-- name    : Couret.STROBO2TORS.recoh_feasible_edge_sets_card_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:51.843398+00:00
-- url     : https://prove2.me/theorems/70c36bd6-24c0-44e0-91ae-45bafdb21520
-- title:
--   At most twenty feasible edge sets arise from six square positions
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Let $U\subseteq G$ be finite with $|U|\le6$ and let $h:G\to\operatorname{Option}(G)$ be arbitrary. A feasible edge set is a three-element subset $E\subseteq U$ for which $h(\sum E)$ returns some value. Then
--
--   $$|\{E\subseteq U:|E|=3,\ h(\sum E)\ne\mathrm{none}\}|\le20.$$
--
--   No correctness contract for the partial halving function is needed for this count.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFastDecoder.lean, lines 120–125; source file SHA-256 d84bc4908e0c9ab4ae54de4f0901e08828a787fa98a3987c63969ea57c85e8da; theorem Couret.STROBO2TORS.recoh_feasible_edge_sets_card_le_twenty

import Aesop
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
import Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a

set_option autoImplicit false

/-!
One-representative RECOH decoder on an explicitly supplied finite support.

The construction visits only the three-element subsets of U.  A supplied
doubling solver chooses one half-sum for each feasible edge set, and a
translation-recovery function turns the corresponding representative into
one candidate.  The final filter uses the complete labelled observation.
No enumeration of the ambient group or its two-torsion subgroup occurs in
these definitions.  Their construction needs no Fintype instance on G.

The refinement theorem proves equality with recohExactDecoder, provided U
covers the observed square support and the half-sum and recovery contracts
hold.  Sign recovery supplies the recovery contract for binary coordinates
inside any larger labelled character bank.  Complex equality remains
noncomputable here: this is a Lean refinement of the mathematical decoder,
not a verification of the external Python parser or arithmetic runtime.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in

theorem recoh_feasible_edge_sets_card_le_twenty
    (U : Finset G) (half : G → Option G) (hU : U.card ≤ 6) :
    (recohFeasibleEdgeSets U half).card ≤ 20 := by sorry












section FiniteRefinement

variable [Fintype G]









end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2











end Couret.STROBO2TORS
