-- Prove2me | Definitions.Def_Applications_NeuralCoding_ChordSwapUniversality
-- name    : Applications_NeuralCoding_ChordSwapUniversality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:53:54.365271+00:00
-- url     : https://prove2.me/theorems/be3b353f-5ae0-44f8-aa9a-42af225a2815
-- title:
--   Aether Catalog definitions — Applications_NeuralCoding_ChordSwapUniversality
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NeuralCoding.ChordSwapUniversality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NeuralCoding/ChordSwapUniversality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Universality of the cubic spectral-gap exponent for weighted swap chains

A *swap chain* on a combinatorial family reconfigures objects by local moves,
and its mixing speed is governed by the **spectral gap** `γ`, the smallest
non-trivial Rayleigh quotient `E(f,f) / Var(f)` of the Dirichlet form.  A previous
cycle isolated the mechanism producing the `n^{-3}` scaling of the fixed-genus
chord-swap gap: on the one-dimensional (path) prototype the *position* statistic
has Dirichlet energy `Θ(n)` and variance `Θ(n⁴)`, so its Rayleigh quotient — and
hence the gap upper bound — is `Θ(n^{-3})`.

The present cycle carries two of the resulting conjectures into unconditional
theorems.

* **Universality (Conjecture 4).**  The cubic exponent is a property of the
  *energy-to-variance ratio*, not of the objects being shuffled.  We prove this
  abstractly: on *any* finite state space, any non-constant test function whose
  Dirichlet energy is at most `c_e · n` and whose variance is at least
  `c_v · n⁴` certifies `γ ≤ (c_e / c_v) · n^{-3}`.  The exponent `3 = 4 − 1` is
  forced by the two growth rates alone.

* **Genus enters only through the constant (Conjecture 3).**  We generalise the
  unit-weight path of the previous cycle to a **conductance-weighted path**, whose
  edges carry a weight `c > 0` that models the effective conductance of a genus.
  The Dirichlet energy scales to `2c(n−1)` while the variance is unchanged, so the
  Rayleigh quotient is exactly `12c / (n²(n+1))`.  The exponent `−3` is therefore
  independent of `c`, and the leading constant is *strictly increasing* in the
  conductance.  Modelling a genus `g` by a strictly decreasing conductance
  `c(g) = 1/(g+1)` then yields a strictly decreasing, strictly positive amplitude
  in front of the invariant `n^{-3}`.

## Main results

* `RQ_le_of_growth`, `gap_le_of_growth`, `gap_cubic_of_linear_quartic` — the
  abstract universality engine: linear energy and quartic variance force a cubic
  Rayleigh quotient and hence a cubic gap upper bound.
* `wpath_dir_eq`, `wpath_vr_eq`, `wpath_RQ_eq` — the conductance-weighted path has
  energy `2c(n−1)`, variance `n²(n²−1)/6`, and Rayleigh quotient `12c/(n²(n+1))`.
  Setting `c = 1` recovers the previous cycle's unit-weight identities.
* `wpath_gap_cubic_upper` and `wpath_RQ_window` — the gap is `O(n^{-3})` and the
  certifying quotient is pinned to `[6c·n^{-3}, 12c·n^{-3}]`, so the exponent is
  exactly three for every fixed conductance.
* `wpath_RQ_strictMono_cond` — the Rayleigh quotient (hence the gap upper bound)
  is strictly increasing in the conductance: the constant, not the exponent,
  carries the dependence.
* `condOfGenus_pos`, `condOfGenus_strictAnti`, `genus_gap_constant_strictAnti` —
  a genus-decreasing conductance produces a strictly decreasing, strictly
  positive leading constant in front of the invariant cubic decay.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  Two claims from the prototype cycle should be
  provable unconditionally in the one-dimensional model: (i) the cubic exponent
  depends only on the linear-energy / quartic-variance profile of the driving
  statistic (universality), and (ii) reweighting the edges — the algebraic shadow
  of changing the effective conductance of a genus — moves the leading constant
  monotonically while leaving the exponent fixed.
* **Experiment (Experimenter).**  Abstracted the Rayleigh calculus over a finite
  state space; proved `RQ_le_of_growth` by `gcongr` from `dir ≤ A` and
  `B ≤ vr`.  Generalised the path energy count to arbitrary edge weight `c`
  (`wpath_dir_eq`, energy `2c(n−1)`), noted the variance is weight-independent
  (`wpath_vr_eq` via the Gauss and square-pyramidal sums), and combined them into
  the exact quotient `12c/(n²(n+1))`.  Strict monotonicity in `c` reduces to a
  single positive-denominator division inequality.
* **Analysis (Analyst).**  Both results are "true and structural".  The exponent
  `3` is a *difference of growth rates* (`4 − 1`) and is manifestly insensitive to
  the multiplicative constant `c`, which is exactly the mechanism by which genus
  can rescale the gap without touching the exponent.  The universality bound is
  the abstract statement of the same arithmetic, stripped of the path.
* **Critique (Critic).**  Is the universality bound vacuous?  No — it consumes a
  genuine non-constant witness and non-negative weights, and produces a bound with
  the correct `n^{-3}` shape whenever the hypotheses are met (verified on the
  weighted path in `example`s below).  Is the monotonicity trivial?  No: it is a
  strict inequality between Rayleigh quotients with a quartic denominator, and it
  is exactly the falsifiable content of "genus enters through the constant".
  Boundary: at `c = 0` the chain disconnects and the quotient collapses to `0`;
  the strict statements therefore require positive conductance, which is recorded
  in the hypotheses.  No theorem references itself; the file builds strictly
  upward.
* **Synthesis (PI).**  The fixed-genus chord-swap programme now has, in the
  one-dimensional model, both the universality principle (Conjecture 4) and the
  genus-through-the-constant principle (Conjecture 3) as theorems.  What remains
  for the genuine diagram space is the combinatorial construction of a monotone,
  unit-step, quartic-variance statistic whose edge weights realise a
  genus-decreasing conductance — at which point these two engines deliver the
  full `γ_{n,g} = c(g)·n^{-3}` picture.
-/

open scoped BigOperators
open Finset

namespace ChordSwapUniv

variable {V : Type*} [Fintype V]

/-! ### Abstract Rayleigh-quotient calculus -/

/-- **Dirichlet energy** of a test function `f` with respect to symmetric,
non-negative edge weights `Q`. -/
def dir (Q : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ x, ∑ y, Q x y * (f x - f y) ^ 2

/-- **Pairwise variation** of `f`: the sum of `(f x − f y)²` over ordered pairs,
equal to `2|V|·Var(f)` under the uniform law. -/
def vr (f : V → ℝ) : ℝ := ∑ x, ∑ y, (f x - f y) ^ 2

/-- **Rayleigh quotient**: energy divided by variation. -/
noncomputable def RQ (Q : V → V → ℝ) (f : V → ℝ) : ℝ := dir Q f / vr f

/-- **Combinatorial spectral gap**: the infimum of the Rayleigh quotient over
non-constant test functions. -/
noncomputable def gap (Q : V → V → ℝ) : ℝ :=
  sInf {r | ∃ f : V → ℝ, (∃ x y, f x ≠ f y) ∧ r = RQ Q f}








/-! ### Universality: linear energy and quartic variance force a cubic quotient -/




/-! ### The conductance-weighted path -/

/-- Symmetric adjacency weights of the length-`n` path with **conductance** `c`:
weight `c` between consecutive positions, `0` otherwise.  Setting `c = 1` recovers
the unit-weight swap graph of the prototype cycle. -/
def wpathQ (c : ℝ) (n : ℕ) : Fin n → Fin n → ℝ :=
  fun x y => if x.val + 1 = y.val ∨ y.val + 1 = x.val then c else 0

/-- The **position** test function `i ↦ i`: a monotone statistic shifted by one
unit per swap. -/
def idf (n : ℕ) : Fin n → ℝ := fun i => (i.val : ℝ)













/-! ### Modelling genus through a decreasing conductance -/

/-- A concrete genus-decreasing conductance: `c(g) = 1/(g+1)`, positive for every
genus and strictly decreasing in `g`. -/
noncomputable def condOfGenus (g : ℕ) : ℝ := 1 / (g + 1)





/-! ### Examples, generalizations, and boundary cases (PEGB) -/

-- Example: the universality engine specialised to the weighted path recovers the
-- exact cubic quotient.
-- Example: the unit-weight energy is `2(n−1)`, generalised by `wpath_dir_eq`.
-- Boundary case: at conductance `c = 0` the chain has no edges, the energy
-- vanishes, and the Rayleigh quotient collapses to `0` — the strict monotonicity
-- and window statements therefore require positive conductance.
end ChordSwapUniv


