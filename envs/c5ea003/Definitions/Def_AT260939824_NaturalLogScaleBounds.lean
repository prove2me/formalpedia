-- Prove2me | Definitions.Def_AT260939824_NaturalLogScaleBounds
-- name    : AT260939824_NaturalLogScaleBounds
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:23:59.383977+00:00
-- url     : https://prove2.me/theorems/8858911c-c1e6-4c8d-bd1d-0c73359d821c
-- title:
--   A natural-log coefficient for carrier height
-- statement:
--   For the integer presentation base $m$ and a natural scale factor $C$, this bundle defines the real coefficient used to compare a discrete logarithmic carrier height with an analytic bound involving the natural logarithm. It keeps the conversion coefficient explicit so later scale choices can track dependence on the presentation base and the horizontal range factor.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/NaturalLogScaleBounds.lean, selected declaration lines 21-22; SHA-256 e1203dcb79e32a75add81caf96323ab270a5494e173f6154f523bd82f112e0cd. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Init
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-! Converting the literal base-`m` carrier height into the analytic scale bound. -/
namespace AbelianTargets
open Filter Topology
noncomputable section



def carrierHeightLogCoefficient (m C : ℕ) : ℝ :=
  (1+Real.log (C : ℝ)/Real.log 2)/Real.log (m : ℝ)+1/Real.log 2





end
end AbelianTargets


