-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_mem_cyclic_coefficient_decoder_iff
-- name    : Couret.STROBO2TORS.recoh_mem_cyclic_coefficient_decoder_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:42:49.369959+00:00
-- url     : https://prove2.me/theorems/8fe84ef5-d4b8-452e-89c5-09052dcda2a4
-- title:
--   Exact membership criterion for cyclic coefficient decoding
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. For any typed square entries $E$, cyclic-bank sparse term lists $L$, and finite $S\subseteq A$, $$S\in D_{\mathrm{cyclic}}(E,L)\iff\operatorname{Format}_{\mathrm{cyclic}}(E,L),\quad |S|=3,\quad\mathcal O_B(S)=\operatorname{TypedObs}(E,L).$$
--
--   Here $B$ is the defined cyclic observed bank. This combines rejection of malformed inputs with exact reconstruction membership.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicCoefficientDecoder.lean, lines 220–234; source file SHA-256 28a7b086d267426fb1e0879ed74d17a1d11a1d82cadf2b7320c0a89680767395; theorem Couret.STROBO2TORS.recoh_mem_cyclic_coefficient_decoder_iff

import Aesop
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_coefficient_decoder_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_input_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An instantiated RECOH decoder on typed observations of cyclic products.

The user supplies only the moduli, labelled square entries, and the observed
coefficient lists.  The primary parameters, exponent encoders, binary
coordinates, doubling solver, square-value function and its covering set
are constructed here.  Their correctness contracts are all discharged.

There is one binary slot for every even factor. Ternary slots occur only
when some factor is even, exactly as for the fixed bank in the Python
decoder. The input guard also imposes moduli at least two, group order at
least three, and the typed numeric/uniqueness checks of its observation
readers. JSON syntax, machine execution and serialization remain separate.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_mem_cyclic_coefficient_decoder_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    S ∈ recohCyclicCoefficientDecoder q entries terms ↔
      RecohCyclicInputFormat q entries terms ∧ S.card = 3 ∧
        recohObservation (recohCyclicObservedBank q) S = recohCyclicTypedObservation q entries terms := by sorry








end Couret.STROBO2TORS
