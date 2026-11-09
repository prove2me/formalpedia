-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_early_coefficient_backend_decoder_card_le_twenty
-- name    : Couret.STROBO2TORS.recoh_early_coefficient_backend_decoder_card_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:49.633005+00:00
-- url     : https://prove2.me/theorems/69910c2f-9b4a-4d29-a7e0-f52d37b3a395
-- title:
--   Early coefficient decoding has at most twenty outputs
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Let $J,K$ be finite bank index types, $U\subseteq G$, $R:G\to\mathbb N$, a partial half solver $h$, an additive equivalence $e:H\simeq(J\to\mathbb F_2)$, natural prime/depth labels and support exponent encodings indexed by $J\sqcup K$, and sparse observed terms on the same indices. If $|U|\le6$, then $$|D_{\mathrm{early}}(U,R,h,e,p,k,\mathrm{enc},\mathrm{obs})|\le20.$$ No semantic correctness or format hypotheses are needed for this size bound.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohEarlySignChecks.lean, lines 184–190; source file SHA-256 00fb65070ccab4cd5989c9c3480f6d3636115ad405abb34a8abb30e6f72a9c7f; theorem Couret.STROBO2TORS.recoh_early_coefficient_backend_decoder_card_le_twenty

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_decoder_card_le_twenty
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

theorem recoh_early_coefficient_backend_decoder_card_le_twenty
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (e : H₂ ≃+ (J → ZMod 2)) (p k : J ⊕ K → ℕ)
    (enc : J ⊕ K → Finset G → List ℕ) (obsTerms : J ⊕ K → RecohSparseTerms)
    (hU : U.card ≤ 6) :
    (recohEarlyCoefficientBackendDecoder U R half e p k enc obsTerms).card ≤ 20 := by sorry


end Couret.STROBO2TORS
