-- Prove2me | Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983
-- name    : Couret_RecohTernaryFibreSelector_4c0db0f29983
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:07:33.400713+00:00
-- url     : https://prove2.me/theorems/29e487af-7589-44e2-8374-2ba431836391
-- title:
--   Ternary probes are constant on ordinary translation orbits
-- statement:
--   Provides the proved fact that every supplied primary-three coordinate character on a product of nonzero cyclic groups has equal support sums on ordinary partners, namely supports differing by a two-torsion translation. This helper is included with the definition dependency bundle because later constructions use its fact directly.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTernaryFibreSelector.lean; source file SHA-256 a19004cdbc2c8dfeac9a2b85c2dced7eb2ccc647c2d5a1cbe660309ae6612e56

import Aesop
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
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
A single concrete ternary coordinate separates the two translation orbits
of any exceptional triple fibre in a product of cyclic groups. The witness
comes from the executable direction selector. The conclusion quantifies over
the entire fibre, so the later square-only search may use any complete set
of orbit representatives rather than knowing the hidden support.
-/

namespace Couret.STROBO2TORS



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_cyclic_ternary_constant_on_ordinary
    (data3 : RecohPrimaryFactorData q 3) (i : RecohPrimaryCoordinate q 3)
    (B C : Finset ((j : Fin d) → ZMod (q j)))
    (h : OrdinaryPartner B C) :
    recohSupportProbe (recohCyclicPrimaryBank q 3 data3 i) B =
      recohSupportProbe (recohCyclicPrimaryBank q 3 data3 i) C := by
  obtain ⟨u, hu, hC⟩ := h
  rw [hC, recoh_support_probe_translate,
    recoh_cyclic_ternary_bank_trivial_on_two q data3 i u hu, one_mul]





end Couret.STROBO2TORS


