-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_observation_check_iff
-- name    : Couret.STROBO2TORS.recoh_sparse_observation_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:11.857435+00:00
-- url     : https://prove2.me/theorems/765f399d-3d15-41a5-ad64-2f1268a8dafa
-- title:
--   The sparse observation check is semantically exact
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. Let the bank have $m$ indices. Assume $R$ vanishes outside finite $U$. For each index use a prime $p_i$, depth $k_i$, a primitive $p_i^{k_i+1}$-st root $\zeta_i$, an exponent-list encoding of $P_{\chi_i}(S)$, and an observed exponent list with root sum $o_i$. Then
--
--   $$\operatorname{SparseObservationCheck}(U,R,p,k,E,\mathrm{obsExp},S)=\mathrm{true}\Longleftrightarrow\operatorname{Obs}(S)=(R,o).$$
--
--   The support $S$ need not have cardinality three for this equivalence.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSparseObservation.lean, lines 111–128; source file SHA-256 3e5ab9ed2f77e232442c1e513ac667674b59190c499be9b6b00defed9b569878; theorem Couret.STROBO2TORS.recoh_sparse_observation_check_iff

import Aesop
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_readings_check_iff
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Executable sparse checking of a full RECOH observation.

The ordered square is checked only on the supplied support of the observed
square together with sums of pairs in the proposed support.  Character
readings are checked by the certified integer-term comparator.  Neither
checker enumerates the ambient group or requires `Fintype G`.

The encodings of proposed and observed readings are input data.  Their
interpretation contracts, the primary orders, primitive roots and support
coverage are explicit hypotheses of correctness.  This module does not
certify a parser or construct those encodings from complex numbers.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_sparse_observation_check_iff {m : ℕ} (U : Finset G) (R : G → ℕ)
    (p k : Fin m → ℕ) (enc : Fin m → Finset G → List ℕ)
    (obsExp : Fin m → List ℕ) (S : Finset G)
    (bank : Fin m → AddChar G ℂ) (ζ obs : Fin m → ℂ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (henc : ∀ i, ((enc i S).map (ζ i ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, ((obsExp i).map (ζ i ^ ·)).sum = obs i) :
    recohSparseObservationCheck U R p k enc obsExp S = true ↔
      recohObservation bank S = (R, obs) := by sorry



end Couret.STROBO2TORS
