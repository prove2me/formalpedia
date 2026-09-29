-- Prove2me | Definitions.Def_Probability_GeneralMixtureWindowLaw
-- name    : Probability_GeneralMixtureWindowLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:53.807198+00:00
-- url     : https://prove2.me/theorems/fe70fa1b-06d8-4d08-8893-4577bc32d35f
-- title:
--   Aether Catalog definitions — Probability_GeneralMixtureWindowLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.GeneralMixtureWindowLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/GeneralMixtureWindowLaw.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
/-
  # The window law for arbitrary exponent heterogeneity

  `Probability.HarmonicBulkSteeperEdgeStrict` proves that the window-implied exponent of a
  *two-component* power-law kernel is strictly antitone in the window width.  Nothing in
  that proof used the number two: it used only that the kernel-to-power-law ratio is
  strictly convex in `log k`.  This file carries the argument out for an arbitrary finite
  positive combination of power laws

  `k ↦ ∑ i ∈ s, w i · k ^ (-e i)`,

  and shows that the antitone window law is a signature of *exponent heterogeneity as
  such*: it holds as soon as two of the exponents differ, with any number of components and
  any positive weights.

  * `genRatio_strict_log_convex` — strict convexity in the logarithmic index, from the
    two-power lemmas of `HarmonicBulkSteeperEdgeStrict` plus a strict sum comparison.
  * `genRatio_lt_of_crossed_strict` — strict no-return past a weak crossing.
  * `genHeadMass_strict_single_crossing` — a pure power law matching the mixture's head mass
    on a window reports strictly less head mass on every narrower window.
  * `gen_implied_exponent_strictAnti` — the window-implied exponent is strictly antitone.
  * `two_component_gen_implied_exponent_strictAnti` — the two-component theorem recovered as
    the instance `s = {0, 1}`, confirming the generalisation is faithful.
-/

open Finset

namespace HarmonicBulkSteeperEdge

variable {ι : Type*}

/-! ## A finite positive combination of power laws -/

/-- A finite positive combination of power-law kernels: weights `w i > 0` and exponents
`e i`. -/
noncomputable def genKernel (s : Finset ι) (w e : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ s, w i * pw (e i) k

/-- Head sum of a general mixture over the window `{1, …, m}`. -/
noncomputable def genHeadSum (s : Finset ι) (w e : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, genKernel s w e k

/-- Head mass of a general mixture: the fraction of the weight on `{1,…,n}` carried by
`{1,…,m}`. -/
noncomputable def genHeadMass (s : Finset ι) (w e : ι → ℝ) (n m : ℕ) : ℝ :=
  genHeadSum s w e m / genHeadSum s w e n

/-- Ratio of the general mixture to the pure power law with exponent `c`. -/
noncomputable def genRatio (s : Finset ι) (w e : ι → ℝ) (c : ℝ) (k : ℕ) : ℝ :=
  genKernel s w e k / pw c k




/-! ## Strict log-convexity for an arbitrary heterogeneous mixture -/




/-! ## The window law -/





end HarmonicBulkSteeperEdge


