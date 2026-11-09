-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_early_readings_check_iff
-- name    : Couret.STROBO2TORS.recoh_early_readings_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:41.227272+00:00
-- url     : https://prove2.me/theorems/30e5c38c-99ac-4844-aca7-51bfdabd31e4
-- title:
--   Early coefficient checks mean binary signs and exact ternary readings
-- statement:
--   Let $G$ be an abelian group and $J,K$ finite types. For each index $i\in J\sqcup K$, let $p_i$ be prime, $k_i$ natural, $\zeta_i$ a primitive $p_i^{k_i+1}$th root, $\chi_i$ a complex additive character, and $L_i$ an integer coefficient list with exponents below $(p_i-1)p_i^{k_i}$. Interpret $L_i$ as $v_i$ at $\zeta_i$. For a fixed support $B$, assume each exponent encoder $E_i(B)$ sums to $P_{\chi_i}(B)$. Then
--
--   $$\operatorname{EarlyCheck}(B)=\mathrm{true}\iff[\forall j\in J,\ v_j=\pm P_{\chi_j}(B)]\land[\forall k\in K,\ v_k=P_{\chi_k}(B)].$$
--
--   The blocks need not have primes two and three for this comparison identity.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohEarlySignChecks.lean, lines 43–68; source file SHA-256 00fb65070ccab4cd5989c9c3480f6d3636115ad405abb34a8abb30e6f72a9c7f; theorem Couret.STROBO2TORS.recoh_early_readings_check_iff

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_match_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_match_neg_iff
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

omit [DecidableEq G] in

theorem recoh_early_readings_check_iff
    (p k : J ⊕ K → ℕ) (enc : J ⊕ K → Finset G → List ℕ)
    (obsTerms : J ⊕ K → RecohSparseTerms) (B : Finset G)
    (bank : J ⊕ K → AddChar G ℂ) (ζ obs : J ⊕ K → ℂ)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i) :
    recohEarlyReadingsCheck p k enc obsTerms B = true ↔
      (∀ j : J, obs (Sum.inl j) = recohSupportProbe (bank (Sum.inl j)) B ∨
        obs (Sum.inl j) = -recohSupportProbe (bank (Sum.inl j)) B) ∧
      (∀ j : K, obs (Sum.inr j) = recohSupportProbe (bank (Sum.inr j)) B) := by sorry














end Couret.STROBO2TORS
