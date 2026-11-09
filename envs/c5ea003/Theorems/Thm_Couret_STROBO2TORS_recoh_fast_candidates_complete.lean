-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_fast_candidates_complete
-- name    : Couret.STROBO2TORS.recoh_fast_candidates_complete
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:52.557611+00:00
-- url     : https://prove2.me/theorems/a22eb41c-472d-47c8-8a26-e94310eb6c96
-- title:
--   Fast candidates contain every compatible triple
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. For a finite set $U\subseteq G$, a partial halving function $h:G\to G\cup\{\mathrm{none}\}$ and a recovery map $f$, fast candidates are $f(\{\sigma-e:e\in E\})$ for three-subsets $E\subseteq U$ on which $h(\sum E)=\sigma$ is defined. Assume the halving function is sound and complete, $U$ contains every point where the observed square $R$ is nonzero, and recovery preserves triple cardinality and returns $B+u$ whenever $|B|=3$, $2u=0$ and $\operatorname{Obs}(B+u)=(R,o)$. Then for every triple $S$ with that observation,
--
--   $$S\in\operatorname{FastCandidates}(U,h,f).$$
--
--   This is completeness of the fast candidate generator.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFastDecoder.lean, lines 172–201; source file SHA-256 d84bc4908e0c9ab4ae54de4f0901e08828a787fa98a3987c63969ea57c85e8da; theorem Couret.STROBO2TORS.recoh_fast_candidates_complete

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





































section FiniteRefinement

variable [Fintype G]

theorem recoh_fast_candidates_complete {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (hhalf : RecohHalfSolverSpec half)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hU : recohSquareSupport obs.1 ⊆ U)
    (S : Finset G) (hS : S.card = 3) (hobs : recohObservation bank S = obs) :
    S ∈ recohFastCandidates U half recover := by sorry








end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2











end Couret.STROBO2TORS
