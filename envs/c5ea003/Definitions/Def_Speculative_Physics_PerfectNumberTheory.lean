-- Prove2me | Definitions.Def_Speculative_Physics_PerfectNumberTheory
-- name    : Speculative_Physics_PerfectNumberTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:40.130891+00:00
-- url     : https://prove2.me/theorems/af122276-942b-4d25-9887-86105696ec6e
-- title:
--   Aether Catalog definitions — Speculative_Physics_PerfectNumberTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Physics.PerfectNumberTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Physics/PerfectNumberTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Physics.PerfectNumberTheory

Auto-generated from theorem catalog database.
Domain: Physics
Declarations: 11
-/

/-- The divisor sum function σ(n). -/
def divisorSum' (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun d => d ∣ n)).sum id

/-- A number is perfect if σ(n) = 2n. -/
def IsPerfect' (n : ℕ) : Prop := divisorSum' n = 2 * n


