-- Prove2me | Theorems.Thm_hasPolychromColouring_mBound
-- name    : hasPolychromColouring_mBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:17.7668+00:00
-- url     : https://prove2.me/theorems/72d0924b-7beb-4ad0-868b-e96a808cbe90
-- title:
--   has Polychrom Colouring m Bound: has Polychrom Colouring m Bound
-- statement:
--   For `k ≥ 4` and sets of size at least `mBound k`, a `k`-colouring exists.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L452-L459
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L452-L459

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
open Asymptotics Filter Topology

theorem hasPolychromColouring_mBound {S : Finset G} {k : ℕ} (hk : 4 ≤ k) (hS : mBound k ≤ #S) :
    HasPolychromColouring (Fin k) S := by sorry
