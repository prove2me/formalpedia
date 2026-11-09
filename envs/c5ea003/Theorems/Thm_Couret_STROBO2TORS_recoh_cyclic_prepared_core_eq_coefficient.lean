-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_prepared_core_eq_coefficient
-- name    : Couret.STROBO2TORS.recoh_cyclic_prepared_core_eq_coefficient
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:14.549201+00:00
-- url     : https://prove2.me/theorems/22d09e7f-c231-469b-a0cb-ff940f0ebdc8
-- title:
--   Early prepared cyclic checks preserve coefficient-core decoding
-- statement:
--   Let $d\in\mathbb N$ and let $q_0,\ldots,q_{d-1}$ be positive natural moduli. Put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. The primary-$p$ coordinate bank uses the standard character at the full $p$-power factor of each modulus divisible by $p$, with supplied factorization $q_j=p^{k_j+1}c_j$ and $\gcd(p,c_j)=1$. For arbitrary sparse square entries $E$ and reduced observed coefficient lists $L_i$ at the canonical bank primes and depths,
--
--   $$\operatorname{PreparedCore}(q,E,L)=\operatorname{CoefficientCore}(q,E,L).$$
--
--   This validates the early-check control flow without requiring the full input-format predicate.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicPreparedDecoder.lean, lines 35–61; source file SHA-256 ce438f7797a7d8114b2cc91e6f9398133f55bd0477b80c4f3fbaf12545a1e818; theorem Couret.STROBO2TORS.recoh_cyclic_prepared_core_eq_coefficient

import Aesop
import Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_bank_encoding_interpret
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_bank_prime
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_bank_root_primitive
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_bank_sign_coordinates
import Theorems.Thm_Couret_STROBO2TORS_recoh_early_coefficient_backend_decoder_eq_backend
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
import Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb

set_option autoImplicit false

/-!
The concrete cyclic decoder with early square and reading checks.

All bank parameters, coefficient encodings, binary coordinates, and square
support data are constructed by the cyclic interface.  This module uses
those data in the early-rejection control flow: check the representative's
square and binary/ternary readings, recover its translation, then retain the
independent full final check.  The guarded decoder is equal to the complete
typed coefficient decoder for every input, including rejected input.

The equality relates executable Lean definitions on typed data.  It does
not identify the external Python parser, caches, or runtime with those
definitions, nor does the candidate bound assert bit complexity.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_cyclic_prepared_core_eq_coefficient
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hred : ∀ i, RecohCoefficientsReduced
      (recohCyclicBankPrime q i) (recohCyclicBankDepth q i) (terms i)) :
    recohCyclicPreparedCore q entries terms = recohCyclicCoefficientCore q entries terms := by sorry














end Couret.STROBO2TORS
