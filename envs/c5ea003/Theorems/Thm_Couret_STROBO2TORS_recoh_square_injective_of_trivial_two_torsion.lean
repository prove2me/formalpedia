-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_square_injective_of_trivial_two_torsion
-- name    : Couret.STROBO2TORS.recoh_square_injective_of_trivial_two_torsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:14.804793+00:00
-- url     : https://prove2.me/theorems/cd0dfa13-0c85-4cde-a8d6-a83d51fc805e
-- title:
--   Trivial two-torsion makes triple square data injective
-- statement:
--   Let $G$ be an abelian group. Assume $2u=0$ implies $u=0$. Then
--
--   $$S\longmapsto Q_S\text{ is injective on three-element finite supports}.$$
--
--   The ambient group need not be finite. This is reconstruction from the ordered square alone.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohOptimalBank.lean, lines 29–40; source file SHA-256 eefa340afa430ea5481039b5dcc716ba178daf20a3ab3a669e9ff87e2565a8d5; theorem Couret.STROBO2TORS.recoh_square_injective_of_trivial_two_torsion

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a

set_option autoImplicit false

/-!
The optimal size of a fixed bank of individual, labelled complex
Fourier coefficients, given the labelled ordered convolution square of a
three-element support.  Zero is allowed in the support.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_square_injective_of_trivial_two_torsion
    (h2 : ∀ u : G, u + u = 0 → u = 0) :
    Function.Injective (fun S : {S : Finset G // S.card = 3} => orderedSquare S.1) := by sorry


variable [Fintype G]









end Couret.STROBO2TORS
