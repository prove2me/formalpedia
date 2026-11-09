-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_representative_checked_decoder_eq_exact
-- name    : Couret.STROBO2TORS.recoh_representative_checked_decoder_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:53:03.328517+00:00
-- url     : https://prove2.me/theorems/06046002-d38d-43ef-97cb-7c240374585b
-- title:
--   A complete representative cover suffices for exact checked decoding
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $R_S$ the ordered pair-sum count of a finite support, and $P_\chi(S)=\sum_{s\in S}\chi(s)$. Assume $G$ finite. Let $o=(R,v)$ be an observation for a bank $\chi_i$, and let a finite representative set $D$ consist of triples with square $R$ such that every triple of square $R$ is $B+u$ for some $B\in D$, $u\in H$. Let $r$ preserve triple size and recover each translate $B+u$ whenever its full observation equals $o$. Let a Boolean checker accept exactly the supports with observation $o$. Then
--
--   $$\operatorname{RepresentativeDecoder}(D,r,\operatorname{check})=\{S:|S|=3,\operatorname{Obs}(S)=o\}.$$
--
--   The cover and recovery conditions are explicit contracts.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDecoder.lean, lines 60–72; source file SHA-256 9726528ae3811835f453edf79765026c8ce160b6454c01ab77b6971e40840b98; theorem Couret.STROBO2TORS.recoh_representative_checked_decoder_eq_exact

import Aesop
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_representative_checked_decoder_iff
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517

set_option autoImplicit false

/-!
Coefficient decoding from the compact parity family.

The generic bridge uses a proved cover modulo two-torsion, the historical
sign-recovery specification and the exact integer observation checker.
The new candidate construction is an image of the parity family, not the
historical edge-triple enumeration. Definitions enumerate neither G nor
its two-torsion subgroup. Complex values occur only in the specification.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

theorem recoh_representative_checked_decoder_eq_exact [Fintype G]
    (reps : Finset (Finset G)) (recover : Finset G → Finset G)
    (check : Finset G → Bool) (bank : I → AddChar G ℂ)
    (obs : (G → ℕ) × (I → ℂ))
    (hcover : RecohParityCover obs.1 reps)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hcheck : ∀ S, check S = true ↔ recohObservation bank S = obs) :
    recohRepresentativeCheckedDecoder reps recover check = recohExactDecoder bank obs := by sorry






variable [Fintype I]







section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





































































end CyclicSelected

end Couret.STROBO2TORS
