-- Prove2me | Definitions.Def_Novelty_Brenier
-- name    : Novelty_Brenier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:06.721319+00:00
-- url     : https://prove2.me/theorems/818f344d-b598-4634-9dd7-95f9e388012f
-- title:
--   Aether Catalog definitions — Novelty_Brenier
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Brenier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Brenier.lean by skeleton subtraction
import Mathlib

/-!
# Discrete Brenier theorem for quadratic cost

Brenier's theorem states that for the quadratic cost the optimal transport map is
the gradient of a convex function — in dimension one, a *monotone* map.  We prove
the finite/discrete avatar of this fact: among all permutation couplings of two
finite point clouds `x, y : Fin n → ℝ`, the quadratic transport cost
`∑ i, (x i - y (σ i))^2` is minimized by the **monotone** matching `σ = id`,
provided `x` and `y` are sorted the same way (`Monovary x y`).

The proof reduces, after expanding the square and using that permutations preserve
`∑ (y ·)^2`, to the rearrangement inequality: a monovarying pair maximizes its
correlation `∑ x i * y i` over all permutations.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Brenier's "optimal map is monotone" should, in the
finite quadratic case, be exactly the rearrangement inequality in disguise.
Experiment (Experimenter): expand `(x i - y (σ i))^2 = x i^2 - 2 x i y(σ i) +
y(σ i)^2`; reindex `∑ y(σ i)^2 = ∑ y i^2` by the permutation; the cost difference
collapses to `2 (∑ x i y i - ∑ x i y(σ i)) ≥ 0`, which is rearrangement.
Analysis (Analyst): the monotonicity hypothesis enters only through `Monovary x y`;
without it the monotone matching need not be optimal (counterexample: `x` increasing,
`y` decreasing — then the *reversing* permutation is optimal), confirming the
hypothesis is load-bearing rather than decorative.
Critique (Critic): we phrase optimality over permutations, the discrete analogue of
optimal *maps*; lifting to all couplings would require Birkhoff–von Neumann, which
is absent from Mathlib and left to future work.
-- !-- end Lab Notes -- !--
-/

namespace Novelty.OptimalTransport

open scoped BigOperators

variable {n : ℕ}

/-- Quadratic transport cost of matching `x i` to `y (σ i)`. -/
def quadraticMatchingCost (x y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, (x i - y (σ i)) ^ 2

/-
**Discrete Brenier theorem (quadratic cost).** If the source points `x` and the
target points `y` are sorted the same way (`Monovary x y`), then the monotone
matching `σ = id` minimizes the quadratic transport cost among all permutation
couplings.
-/


end Novelty.OptimalTransport


