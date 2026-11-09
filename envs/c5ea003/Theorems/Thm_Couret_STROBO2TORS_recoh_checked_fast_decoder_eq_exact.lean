-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_checked_fast_decoder_eq_exact
-- name    : Couret.STROBO2TORS.recoh_checked_fast_decoder_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:46:21.135771+00:00
-- url     : https://prove2.me/theorems/4a1c2a9a-9459-4f61-a16a-a70560b0c328
-- title:
--   A checked fast decoder equals exact observation filtering
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a finite support $S$, and $P_\chi(S)=\sum_{s\in S}\chi(s)$ its complex character reading. Write $O(S)=\{S+u:2u=0\}$. Assume $G$ is finite. Let $\chi_i$ be a bank, $o=(R,v)$ an observation, and $U\subseteq G$ contain every point where $R$ is nonzero. Let $h:G\to\operatorname{Option}(G)$ return only valid halves and return one whenever a half exists. Let $r$ map triples to triples and satisfy: whenever $2u=0$ and the full observation of $B+u$ equals $o$, then $r(B)=B+u$. Let a Boolean checker accept exactly supports whose full observation equals $o$. Then
--
--   $$\operatorname{CheckedFast}(U,h,r,\operatorname{check})=\{S:|S|=3,\ (R_S,(P_{\chi_i}(S))_i)=o\}.$$
--
--   The halving, recovery, support-coverage and final-check contracts are explicit hypotheses.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFastDecoder.lean, lines 235–247; source file SHA-256 d84bc4908e0c9ab4ae54de4f0901e08828a787fa98a3987c63969ea57c85e8da; theorem Couret.STROBO2TORS.recoh_checked_fast_decoder_eq_exact

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_fast_candidates_complete
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
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





































section FiniteRefinement

variable [Fintype G]

theorem recoh_checked_fast_decoder_eq_exact {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (check : Finset G → Bool) (bank : I → AddChar G ℂ)
    (obs : (G → ℕ) × (I → ℂ))
    (hhalf : RecohHalfSolverSpec half)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hU : recohSquareSupport obs.1 ⊆ U)
    (hcheck : ∀ S : Finset G, check S = true ↔ recohObservation bank S = obs) :
    recohCheckedFastDecoder U half recover check = recohExactDecoder bank obs := by sorry


end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2











end Couret.STROBO2TORS
