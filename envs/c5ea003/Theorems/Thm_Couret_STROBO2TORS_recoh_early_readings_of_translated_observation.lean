-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_early_readings_of_translated_observation
-- name    : Couret.STROBO2TORS.recoh_early_readings_of_translated_observation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:27:53.340865+00:00
-- url     : https://prove2.me/theorems/f7342b99-1a78-4112-a2aa-dfa5768b42ef
-- title:
--   Translated observations pass the early reading check
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S$ counts ordered sums and $B$ is a bank of complex additive characters. Let the bank indices be $J\sqcup K$, with prime labels $p_i$, depths $k_i\ge0$, primitive roots $\zeta_i$ of order $p_i^{k_i+1}$, support exponent encodings $E_i$, reduced sparse observed terms $L_i$ (all exponents below $(p_i-1)p_i^{k_i}$), complex observations $o_i$, and an additive equivalence $e:H\simeq(J\to\mathbb F_2)$. Fix a finite support $S$. Assume its exponent encodings evaluate to its bank probes and $L_i$ evaluates to $o_i$. On $H$, assume the $J$ characters satisfy $\chi_j(u)=(-1)^{e(u)_j}$ and the $K$ characters are identically one. If $u\in H$ satisfies $P_{\chi_i}(S+u)=o_i$ for every index, then $$\operatorname{EarlyReadingsCheck}(p,k,E,L,S)=\mathrm{true}.$$ No three-element premise is imposed on $S$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohEarlySignChecks.lean, lines 70–101; source file SHA-256 00fb65070ccab4cd5989c9c3480f6d3636115ad405abb34a8abb30e6f72a9c7f; theorem Couret.STROBO2TORS.recoh_early_readings_of_translated_observation

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_early_readings_check_iff
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

theorem recoh_early_readings_of_translated_observation
    (p k : J ⊕ K → ℕ) (enc : J ⊕ K → Finset G → List ℕ)
    (obsTerms : J ⊕ K → RecohSparseTerms)
    (bank : J ⊕ K → AddChar G ℂ) (ζ obs : J ⊕ K → ℂ)
    (e : H₂ ≃+ (J → ZMod 2))
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (B : Finset G)
    (henc : ∀ i, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (hcoord : ∀ (u : H₂) (j : J),
      bank (Sum.inl j) (u : G) = if e u j = 0 then 1 else -1)
    (hternary : ∀ (u : H₂) (j : K), bank (Sum.inr j) (u : G) = 1)
    (u : H₂)
    (hreadings : ∀ i, recohSupportProbe (bank i) (translateSupport B (u : G)) = obs i) :
    recohEarlyReadingsCheck p k enc obsTerms B = true := by sorry












end Couret.STROBO2TORS
