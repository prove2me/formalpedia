-- Prove2me | Theorems.Thm_DiophantineLattice_sum_sq_sub_self_even
-- name    : DiophantineLattice.sum_sq_sub_self_even
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:27:50.921991+00:00
-- url     : https://prove2.me/theorems/ba831d73-c475-43c5-8dfe-8cac7c5f2245
-- title:
--   Completing the square for the standard form at the deep hole turns `F` into
-- statement:
--   Completing the square for the standard form at the deep hole turns `F` into
--   `Σ (xᵢ² - xᵢ) + c`; the quadratic part is always an **even non-negative** integer.
--
--   ```lean
--   theorem DiophantineLattice.sum_sq_sub_self_even(m : Fin n → ℤ) :
--       ∃ k : ℤ, 0 ≤ k ∧ (∑ i, ((m i) ^ 2 - m i)) = 2 * k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DiophantineLatticeCompleteSquare.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DiophantineLatticeCompleteSquare.lean#L166

-- Thm stub generated from Novelty/DiophantineLatticeCompleteSquare.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeCompleteSquare
import Definitions.Def_Novelty_DiophantineLatticeTorsionGap

/-!
# Non-homogeneous quadratic forms with a linear term: completing the square

Cycle 3.  The classical non-homogeneous quadratic Diophantine equation is

  `F(x) = Q(x) + ℓ(x) + c = 0`,  `Q(x) = xᵀBx`, `ℓ(x) = Σ bᵢ xᵢ`,

and the standard manoeuvre is to complete the square: if `s` solves `2·Bil(s, ·) = ℓ`, then
`F(x) = Q(x + s) + (c - Q(s))`, so the solvability of `F = 0` over `ℤⁿ` is governed by the
*spectral gap* of the shifted form studied in the previous two cycles.

* `complete_the_square` : the algebraic identity (needs `B` symmetric only).
* `nonhom_ge_archimedean` : the naive real obstruction `F(x) ≥ c - Q(s)`.
* `nonhom_ge_torsion` : the lattice refinement, `F(x) ≥ λ₁/r² + c - Q(s)`, valid when `-s` is
  the `r`-torsion point `v/r` of a shortest vector `v`.
* `nonhom_unsolvable_of_pos` : consequently, when `s = -v/r`, the equation `F = 0` has **no**
  integral solution as soon as `c > 0` — whereas the archimedean criterion only rules out
  `c > λ₁/r²`.  The lattice gap improves the classical criterion by exactly `λ₁/r²`.
* `sum_sq_sub_self_even` and `sum_sq_sub_self_eq_zero_iff_of_pos` : the concrete arithmetic
  payoff in the standard case, `Σ (xᵢ² - xᵢ)` is always an even non-negative integer, so
  `Σ (xᵢ² - xᵢ) + c = 0` forces `c` to be a non-positive even integer.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the `λ₁/r²` gap should be visible as a strict improvement of the
classical "complete the square and use positivity" unsolvability criterion.
Experiment (Experimenter): completing the square at `s = -v/2` for the standard form in
dimension `n` turns `F` into `Σ(xᵢ² - xᵢ) + c`; enumeration (`ComputationalEvidence.md`, §1)
shows `Σ(xᵢ² - xᵢ) ∈ {0, 2, 4, …}` — the archimedean bound `≥ -n/4` is off by the whole gap.
Analysis (Analyst): the improvement is exactly `Q(s) = λ₁/r²`, i.e. the archimedean bound
`c - Q(s)` is replaced by `c`; the residual arithmetic (evenness) is the `2`-adic phenomenon of
cycle 1, imported here through `deepHole_spectrum`.
Critique (Critic): `complete_the_square` needs the hypothesis that `ℓ` is in the image of
`2·Bil`, which we take as an explicit hypothesis rather than inverting `B`; this is exactly the
condition for the shift to be rational, and it is non-vacuous (`standard_linear_shift`).
Synthesis (PI): completing the square is the bridge that turns every cycle-1/2 gap theorem into
an unsolvability criterion for a genuine non-homogeneous Diophantine equation.
-/

open DiophantineLattice

open Finset

variable {n : ℕ}










/-! ## Non-vacuity: the standard form admits such shifts -/





/-! ## The concrete standard case: `Σ (xᵢ² - xᵢ) + c = 0` -/

theorem DiophantineLattice.sum_sq_sub_self_even(m : Fin n → ℤ) :
    ∃ k : ℤ, 0 ≤ k ∧ (∑ i, ((m i) ^ 2 - m i)) = 2 * k := by sorry
