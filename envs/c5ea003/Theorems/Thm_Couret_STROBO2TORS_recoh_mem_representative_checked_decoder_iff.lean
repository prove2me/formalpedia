-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_mem_representative_checked_decoder_iff
-- name    : Couret.STROBO2TORS.recoh_mem_representative_checked_decoder_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:45:52.856631+00:00
-- url     : https://prove2.me/theorems/1b710d58-61c7-48ca-a8cb-5be911674ad6
-- title:
--   Checked representatives give exact decoder membership
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S$ counts ordered sums and $B$ is a bank of complex additive characters. Let $\mathcal R$ be a finite support family sound for square function $R$ and covering every three-element realization of $R$ up to $H$ translation. Let $f$ preserve cardinality three and recover every $H$-translate of every triple that realizes the fixed full observation $o=(R,(o_i))$. Let Boolean $c(S)$ mean exactly $\mathcal O_B(S)=o$. Then for every finite $S$, $$S\in\{f(C):C\in\mathcal R,\ c(f(C))=\mathrm{true}\}\iff |S|=3\text{ and }\mathcal O_B(S)=o.$$
--
--   This is exact membership for the defined representative-checked decoder.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDecoder.lean, lines 36–58; source file SHA-256 9726528ae3811835f453edf79765026c8ce160b6454c01ab77b6971e40840b98; theorem Couret.STROBO2TORS.recoh_mem_representative_checked_decoder_iff

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

theorem recoh_mem_representative_checked_decoder_iff
    (reps : Finset (Finset G)) (recover : Finset G → Finset G)
    (check : Finset G → Bool) (bank : I → AddChar G ℂ)
    (obs : (G → ℕ) × (I → ℂ))
    (hcover : RecohParityCover obs.1 reps)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hcheck : ∀ S, check S = true ↔ recohObservation bank S = obs)
    (S : Finset G) :
    S ∈ recohRepresentativeCheckedDecoder reps recover check ↔
      S.card = 3 ∧ recohObservation bank S = obs := by sorry








variable [Fintype I]







section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





































































end CyclicSelected

end Couret.STROBO2TORS
