-- Prove2me | Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497
-- name    : Couret_RecohFibreOptimal_b9d6825ce497
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:20.413272+00:00
-- url     : https://prove2.me/theorems/c72c3b40-b3e2-46ea-9821-c097c38fc80f
-- title:
--   Character-query budgets for an observed square fibre
-- statement:
--   Defines the fibre budget as the base-two natural logarithm of its cardinality, and the after-square budget as zero when the two-torsion rank $r$ is zero, otherwise $r+\min(1,s)$ where $s$ is the three-torsion rank. Defines an observation consisting of the ordered square and character readings from a bank selected solely from that square.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreOptimal.lean; source file SHA-256 609b61fbff59a0b55eb1cdb79538dc43bc1d0ed28d4633216dc67d9b09fe3bac

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
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
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
Optimal character banks selected from the observed labelled ordered square.
The selected bank is fixed on its entire fibre. Selection is existential;
this module does not implement selection from raw or typed decoder input.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The integer information budget of a complete square fibre. For a triple
the fibre size is a power of two, so the logarithm is exact. -/
def recohFibreBudget (S : Finset G) : ℕ := Nat.log 2 (squareFibre S).card













/-- Worst-case budget when the bank can be selected from the observed square. -/
def recohAfterSquareBudget (r s : ℕ) : ℕ :=
  if r = 0 then 0 else r + min 1 s



/-- A square-selected bank together with the square itself is the complete
observation. Equal squares select exactly the same bank. -/
def recohSquareSelectedObservation {k : ℕ}
    (select : (G → ℕ) → (Fin k → AddChar G ℂ)) (S : Finset G) :
    (G → ℕ) × (Fin k → ℂ) :=
  (orderedSquare S, fun i => recohSupportProbe (select (orderedSquare S) i) S)















end Couret.STROBO2TORS


