-- Prove2me | Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
-- name    : Couret_RecohOptimalBank_e8b60aaa0883
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:57.570429+00:00
-- url     : https://prove2.me/theorems/ebc44b62-491d-4dd2-822d-92e92accf392
-- title:
--   The fixed-bank optimal query budget
-- statement:
--   For natural torsion ranks $r,s$, defines the budget to be zero if $r=0$, and $r+s$ otherwise. This is the numerical budget used for a single fixed bank of labelled complex character coefficients accompanying the labelled ordered square; the definition alone asserts no optimality theorem.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohOptimalBank.lean; source file SHA-256 eefa340afa430ea5481039b5dcc716ba178daf20a3ab3a669e9ff87e2565a8d5

import Aesop
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





variable [Fintype G]





/-- The budget is zero without two-torsion, and the sum of the two- and
three-torsion ranks otherwise. -/
def recohOptimalBudget (r s : ℕ) : ℕ := if r = 0 then 0 else r + s



end Couret.STROBO2TORS


