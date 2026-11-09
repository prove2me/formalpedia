-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_early_coefficient_backend_decoder_eq_backend
-- name    : Couret.STROBO2TORS.recoh_early_coefficient_backend_decoder_eq_backend
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:06.516822+00:00
-- url     : https://prove2.me/theorems/a0f9715f-3b6d-400d-a9d1-b0940ff13119
-- title:
--   Early coefficient checks preserve the backend result
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. Let the finite bank index set split as $J\sqcup K$, with binary equivalence $e:G[2]\cong\mathbb F_2^J$. Use prime-depth roots, reduced coefficient observation data, and correct exponent encodings for every finite support. Assume the square data vanish outside $U$, the binary characters restrict to the signs given by $e$, and all characters indexed by $K$ are one on $G[2]$. For any partial halving function,
--
--   $$\operatorname{EarlyCoefficientBackend}(U,R,h,e,p,k,E,T)=\operatorname{CoefficientBackend}(U,R,h,\mathrm{inl},e,p,k,E,T).$$
--
--   Thus early pruning preserves the final candidate set without requiring a correctness premise on the halving function.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohEarlySignChecks.lean, lines 153–182; source file SHA-256 00fb65070ccab4cd5989c9c3480f6d3636115ad405abb34a8abb30e6f72a9c7f; theorem Couret.STROBO2TORS.recoh_early_coefficient_backend_decoder_eq_backend

import Aesop
import Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_readings_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_early_readings_of_translated_observation
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_recover_support_square
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_decoder_eq_checked
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5

set_option autoImplicit false

/-!
Early rejection of incompatible binary and ternary readings.

The bank index is J ⊕ K.  The intended cyclic bank uses prime two on J and
prime three on K.  The executable tests retain the supplied prime parameters;
their correctness uses explicit primary-representation contracts and the two
roles on G[2]: signs on J, trivial character values on K.

Binary observations must equal the representative reading or its negative;
ternary observations must equal the representative reading.  These are exact
integer-coefficient comparisons.  A final accepted recovered support always
passes these early tests, without nonvanishing or cardinality assumptions.
Combining them with the early square check therefore preserves the answer of
the full coefficient backend.  This proves an order of typed mathematical
operations, not the external Python parser, cache, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G J K : Type*} [AddCommGroup G] [DecidableEq G]
variable [Fintype J] [Fintype K]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

theorem recoh_early_coefficient_backend_decoder_eq_backend
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (e : H₂ ≃+ (J → ZMod 2)) (p k : J ⊕ K → ℕ)
    (enc : J ⊕ K → Finset G → List ℕ) (obsTerms : J ⊕ K → RecohSparseTerms)
    (bank : J ⊕ K → AddChar G ℂ) (ζ obs : J ⊕ K → ℂ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i S, ((enc i S).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (hcoord : ∀ (u : H₂) (j : J),
      bank (Sum.inl j) (u : G) = if e u j = 0 then 1 else -1)
    (hternary : ∀ (u : H₂) (j : K), bank (Sum.inr j) (u : G) = 1) :
    recohEarlyCoefficientBackendDecoder U R half e p k enc obsTerms =
      recohCoefficientBackendDecoder U R half Sum.inl e p k enc obsTerms := by sorry




end Couret.STROBO2TORS
