-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_backend_decoder_card_le_twenty
-- name    : Couret.STROBO2TORS.recoh_sparse_backend_decoder_card_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:27.584475+00:00
-- url     : https://prove2.me/theorems/82b472e8-25c6-4f3c-9ba4-11301fab855e
-- title:
--   The sparse exponent backend has at most twenty outputs
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $R_S$ the ordered pair-sum count of a finite support, and $P_\chi(S)=\sum_{s\in S}\chi(s)$. Let $U\subseteq G$ with $|U|\le6$, a function $R:G\to\mathbb N$, an arbitrary partial halver $h$, and an additive equivalence $e:H\cong(\mathbb Z/2\mathbb Z)^r$ be given. Supply arbitrary binary depths $k_{2,j}$, candidate exponent encoders and observed exponent lists for $j<r$, and arbitrary labels $p_i,k_i$, encoders and observed exponent lists for $i<m$. Then
--
--   $$|\operatorname{SparseBackendDecoder}(U,R,h,e,k_2,E_2,O_2,p,k,E,O)|\le20.$$
--
--   This cardinality bound imposes no semantic correctness or primality assumptions on those inputs.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohExactSignBackend.lean, lines 243–252; source file SHA-256 f99e3408f62032866dd7332e37aea90148e1e51601887993b2026a97b35d79dd; theorem Couret.STROBO2TORS.recoh_sparse_backend_decoder_card_le_twenty

import Aesop
import Definitions.Def_Couret_RecohExactSignBackend_8d2941f5c2c9
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_checked_fast_decoder_card_le_twenty
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Computable comparison bits and their refinement of complex sign recovery.

The comparison booleans are supplied by an exact arithmetic backend.  Only
their correctness proposition mentions complex numbers.  The recovered
coordinate vector and transport through a supplied coordinate equivalence
are ordinary Lean definitions, with no complex equality decision at runtime.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2







variable [DecidableEq G]

theorem recoh_sparse_backend_decoder_card_le_twenty {m : ℕ}
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (e : H₂ ≃+ (Fin r → ZMod 2)) (k2 : Fin r → ℕ)
    (enc2 : Fin r → Finset G → List ℕ) (obs2 : Fin r → List ℕ)
    (p k : Fin m → ℕ) (enc : Fin m → Finset G → List ℕ)
    (obsExp : Fin m → List ℕ) (hU : U.card ≤ 6) :
    (recohSparseBackendDecoder U R half e k2 enc2 obs2 p k enc obsExp).card ≤ 20 := by sorry


end Couret.STROBO2TORS
