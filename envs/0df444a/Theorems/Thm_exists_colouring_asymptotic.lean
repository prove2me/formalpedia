-- Prove2me | Theorems.Thm_exists_colouring_asymptotic
-- name    : exists_colouring_asymptotic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:39:31.911288+00:00
-- url     : https://prove2.me/theorems/548ed78d-9b1a-4e8d-b48b-d11cd16f1d78
-- title:
--   exists colouring asymptotic: exists colouring asymptotic
-- statement:
--   Sets of size `(3 + ε)k log k` have `k`-colourings for sufficiently large `k`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L462-L470
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L462-L470

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

theorem exists_colouring_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ S : Finset G, (3 + ε) * k * log k ≤ #S →
      HasPolychromColouring (Fin k) S := by sorry
