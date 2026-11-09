-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_readings_check_iff
-- name    : Couret.STROBO2TORS.recoh_sparse_readings_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:29:17.496002+00:00
-- url     : https://prove2.me/theorems/faccb141-946d-41b1-9ae8-034d5a3a0f2f
-- title:
--   Sparse exponent comparisons exactly check all character readings
-- statement:
--   Let $G$ be an abelian group, and let $i<m$ index primes $p_i$, depths $k_i$, primitive complex roots $\zeta_i$ of order $p_i^{k_i+1}$, characters $\chi_i$, candidate exponent encoders $E_i$, observed exponent lists $O_i$, and observed values $v_i$. For a fixed support $S$, assume $\sum_{e\in E_i(S)}\zeta_i^e=P_{\chi_i}(S)$ and $\sum_{e\in O_i}\zeta_i^e=v_i$. Then
--
--   $$\operatorname{SparseReadingsCheck}(p,k,E,O,S)=\mathrm{true}\iff(P_{\chi_i}(S))_{i<m}=v.$$
--
--   The exponent lists may contain repetitions and have arbitrary finite lengths.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSparseObservation.lean, lines 79–102; source file SHA-256 3e5ab9ed2f77e232442c1e513ac667674b59190c499be9b6b00defed9b569878; theorem Couret.STROBO2TORS.recoh_sparse_readings_check_iff

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_normalized_sparse_equal_iff
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

omit [DecidableEq G] in

theorem recoh_sparse_readings_check_iff {m : ℕ} (p k : Fin m → ℕ)
    (enc : Fin m → Finset G → List ℕ) (obsExp : Fin m → List ℕ)
    (S : Finset G) (bank : Fin m → AddChar G ℂ) (ζ obs : Fin m → ℂ)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (henc : ∀ i, ((enc i S).map (ζ i ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, ((obsExp i).map (ζ i ^ ·)).sum = obs i) :
    recohSparseReadingsCheck p k enc obsExp S = true ↔
      (fun i => recohSupportProbe (bank i) S) = obs := by sorry







end Couret.STROBO2TORS
