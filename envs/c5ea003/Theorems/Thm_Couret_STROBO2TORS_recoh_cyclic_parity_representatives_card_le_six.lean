-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_parity_representatives_card_le_six
-- name    : Couret.STROBO2TORS.recoh_cyclic_parity_representatives_card_le_six
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:28.077539+00:00
-- url     : https://prove2.me/theorems/335c41d3-2d6c-45b0-84a9-2f3a55595cca
-- title:
--   At most six cyclic parity representatives
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. For every typed square-entry list $E$ in $A\times\mathbb N$, $$|\operatorname{ParityReps}(E)|\le6.$$ No well-formedness or realizability premise is imposed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityOrbitRefinement.lean, lines 101–107; source file SHA-256 185cc0d31c6488113857d44700e65389fdc92fe2ab3f45b213f4e762f52ee979; theorem Couret.STROBO2TORS.recoh_cyclic_parity_representatives_card_le_six

import Aesop
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_representatives_card_le_six
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d
import Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce

set_option autoImplicit false

/-!
Composition of the parity generator with the historical orbit construction.

The equality below is an equality of finite families of entire H-orbits,
not equality of representatives or their iteration order. Deduplication is
applied to an explicit list enumeration of the parity representatives. The
list and its anchors are inputs with stated representation contracts; no
classical `Finset.toList` is hidden in an executable definition.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

omit [∀ i, NeZero (q i)] in
theorem recoh_cyclic_parity_representatives_card_le_six
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    (recohCyclicParityRepresentatives q entries).card ≤ 6 := by sorry




end Cyclic

end Couret.STROBO2TORS
