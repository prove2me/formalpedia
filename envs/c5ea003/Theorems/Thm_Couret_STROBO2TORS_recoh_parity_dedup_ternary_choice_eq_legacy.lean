-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_ternary_choice_eq_legacy
-- name    : Couret.STROBO2TORS.recoh_parity_dedup_ternary_choice_eq_legacy
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:08.155399+00:00
-- url     : https://prove2.me/theorems/32d555f3-2c84-4920-a04f-47b5469d2eed
-- title:
--   Parity deduplication preserves the selected ternary coordinate
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. For typed square entries $E$ on $A$, let $x$ be a list whose finite-set contents equal the cyclic parity representatives. Let an anchor choose a point of each member of $x$. Then the ternary choice computed from its anchored deduplication equals the legacy square-selected ternary choice: $$\operatorname{Choice}(\operatorname{dedup}(x))=\operatorname{SquareChoice}(E).$$ No input-format premise is needed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParitySelector.lean, lines 224–250; source file SHA-256 c17657a92d6caa292995c99fb93b4623634d6b4d95a8fae5ba6263e804ec456a; theorem Couret.STROBO2TORS.recoh_parity_dedup_ternary_choice_eq_legacy

import Aesop
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_cover
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_orbit_families_eq_legacy
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c

set_option autoImplicit false

/-!
Transport of the conditional ternary selector to the parity representatives.

A ternary observation is constant on each two-torsion orbit. Consequently
both the one-orbit predicate and every separating-coordinate predicate
depend only on the finite family of orbits. Scanning the same coordinate
order therefore returns exactly the same first coordinate, even when the
representatives or their deduplication order differ.

The definitions below concern typed mathematical inputs. They do not
identify Python list order, parsing, exceptions, or execution semantics.
-/

namespace Couret.STROBO2TORS

section FiniteFamilies

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







end FiniteFamilies

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_parity_dedup_ternary_choice_eq_legacy
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (hxs : xs.toFinset = recohCyclicParityRepresentatives q entries)
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i)))
    (hanchor : ∀ B ∈ xs, anchor B ∈ B) :
    recohTernaryChoiceFromRepresentatives q (recohAnchoredOrbitDedup anchor xs).toFinset =
      recohSquareTernaryChoice q entries := by sorry


end Cyclic

end Couret.STROBO2TORS
