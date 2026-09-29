-- Prove2me | Theorems.Thm_Novelty_OptimalTransport_brenier_monotone_optimal
-- name    : Novelty.OptimalTransport.brenier_monotone_optimal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:16:13.685137+00:00
-- url     : https://prove2.me/theorems/1f071de5-f6a6-44c3-b167-1d30f37e2bc2
-- title:
--   Brenier monotone optimal
-- statement:
--   Formal statement of `Novelty.OptimalTransport.brenier_monotone_optimal` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Novelty.OptimalTransport.brenier_monotone_optimal(x y : Fin n → ℝ) (h : Monovary x y)
--       (σ : Equiv.Perm (Fin n)) :
--       quadraticMatchingCost x y (Equiv.refl _) ≤ quadraticMatchingCost x y σ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/Brenier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/Brenier.lean#L48

-- Thm stub generated from Novelty/Brenier.lean
import Mathlib
import Definitions.Def_Novelty_Brenier

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

open Novelty.OptimalTransport

open scoped BigOperators

variable {n : ℕ}


/-
**Discrete Brenier theorem (quadratic cost).** If the source points `x` and the
target points `y` are sorted the same way (`Monovary x y`), then the monotone
matching `σ = id` minimizes the quadratic transport cost among all permutation
couplings.
-/

theorem Novelty.OptimalTransport.brenier_monotone_optimal(x y : Fin n → ℝ) (h : Monovary x y)
    (σ : Equiv.Perm (Fin n)) :
    quadraticMatchingCost x y (Equiv.refl _) ≤ quadraticMatchingCost x y σ := by sorry
