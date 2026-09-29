-- Prove2me | Definitions.Def_Algebra_SAWTropical_GrowthRate
-- name    : Algebra_SAWTropical_GrowthRate
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:48:19.966541+00:00
-- url     : https://prove2.me/theorems/f287c9c7-cf6a-455e-a9e0-cf135e06ed18
-- title:
--   Aether Catalog definitions — Algebra_SAWTropical_GrowthRate
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.SAWTropical.GrowthRate`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/SAWTropical/GrowthRate.lean by skeleton subtraction
import Mathlib
/-
# Submultiplicative Growth Rates and the Fekete–Tropical Bridge

This file establishes formal foundations connecting submultiplicative sequences
(as arise in self-avoiding walk enumeration) to subadditive analysis via Fekete's
lemma, and to tropical algebra via growth-rate convergence criteria.

## Main Results

- `IsSubmultiplicative`: A sequence `a : ℕ → ℝ` with `a(m+n) ≤ a(m) * a(n)` and `a(n) > 0`.
- `IsSubmultiplicative.log_subadditive`: Logarithm converts submultiplicative to subadditive.
- `IsSubmultiplicative.bound_pow`: `a(k*n) ≤ a(n)^k * a(0)` for submultiplicative sequences.
- `submulGrowthRate`: The connective constant as infimum of nth roots.
- `TropicalPowerSeries`: Tropical power series and convergence criteria.
- `fekete_tropical_bridge`: The bridge between classical and tropical convergence.
-/

open Real Filter Topology Set

/-! ## Submultiplicative Sequences -/

/-- A sequence `a : ℕ → ℝ` is submultiplicative if `a(m+n) ≤ a(m) * a(n)` for all `m, n`,
    and all values are positive. This captures the growth pattern of self-avoiding walk
    counts on lattices. -/
def IsSubmultiplicative (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 < a n) ∧ (∀ m n, a (m + n) ≤ a m * a n)




/-! ## Growth Rate (Connective Constant) -/

/-- The **growth rate** (or connective constant) of a submultiplicative sequence,
    defined as the infimum of `a(n)^(1/n)` over positive `n`. For self-avoiding walks,
    this is the connective constant `μ` of the lattice. -/
noncomputable def submulGrowthRate (a : ℕ → ℝ) : ℝ :=
  iInf (fun n : ℕ+ => (a n) ^ (1 / (n : ℝ)))



/-
The growth rate is nonneg for submultiplicative sequences.
-/

/-
The growth rate is positive when `a(n) ≥ 1` for all positive `n`. This holds
    for SAW counts, since there is always at least one walk of each length.
-/

/-! ## Tropical Power Series Convergence -/


namespace TropicalPowerSeries


end TropicalPowerSeries

/-! ## The Fekete–Tropical Bridge -/


/-
**Fekete–Tropical Bridge Theorem**: For a submultiplicative sequence with positive
    growth rate, `-log(a(n)) + n * log(μ) ≤ 0` for all positive `n`. This means every
    term of the tropical power series at the growth rate is non-positive, connecting
    the classical radius of convergence `1/μ` to the tropical growth rate `log(μ)`.
-/

/-! ## Self-Avoiding Walk Application -/

/-- A **lattice graph** for SAW enumeration: a type with a symmetric generating set. -/
structure LatticeGraph where
  vertices : Type*
  [grp : Group vertices]
  generators : Finset vertices
  symm : ∀ g ∈ generators, g⁻¹ ∈ generators
  one_not_gen : (1 : vertices) ∉ generators

/-- SAW count data for a lattice graph. -/
structure SAWCount (G : LatticeGraph) where
  count : ℕ → ℝ
  submul : IsSubmultiplicative count
  count_zero : count 0 = 1
  count_one : count 1 = G.generators.card

/-- The **connective constant** of a lattice graph. -/
noncomputable def connectiveConstant (G : LatticeGraph) (c : SAWCount G) : ℝ :=
  submulGrowthRate c.count


/-! ## Nienhuis Constant -/

/-- The Nienhuis constant `√(2 + √2)` — the connective constant of the hexagonal lattice,
    proved by Duminil-Copin and Smirnov (2012). -/
noncomputable def NienhuisConstant : ℝ := Real.sqrt (2 + Real.sqrt 2)


