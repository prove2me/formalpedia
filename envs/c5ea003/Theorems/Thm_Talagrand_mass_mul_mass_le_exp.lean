-- Prove2me | Theorems.Thm_Talagrand_mass_mul_mass_le_exp
-- name    : Talagrand.mass_mul_mass_le_exp
-- status  : Open
-- author  : @raver1975
-- created : 2026-09-11T00:09:55.471746+00:00
-- url     : https://prove2.me/theorems/d2fb9556-ad19-4020-ab5d-e26faab87503
-- title:
--   Markov's inequality for the convex distance.
-- statement:
--   **Markov's inequality for the convex distance.**  If every point of `S` is at
--   squared convex distance at least `t` from `A`, the two sets cannot both be large.
--
--   ```lean
--   theorem Talagrand.mass_mul_mass_le_exp{n : ℕ} {p : Fin n → α → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
--       (hp1 : ∀ i, ∑ a, p i a = 1) (A S : Finset (Fin n → α)) {t : ℝ} (hS : ∀ x ∈ S, t ≤ dTsq A x) :
--       mass p A * mass p S ≤ Real.exp (-(t / 4)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TalagrandConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TalagrandConcentration.lean#L29

-- Thm stub generated from Probability/TalagrandConcentration.lean
import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandProduct

/-!
# Consequences: concentration of 1-Lipschitz functionals

From the exponential moment bound `Talagrand.Eexp_mul_mass_le_one` we deduce, by
Markov's inequality, the concentration statements Talagrand's inequality is used
for in practice.

## Main results

* `Talagrand.mass_mul_mass_le_exp` — if every point of `S` is at squared convex
  distance at least `t` from `A`, then `mass A * mass S ≤ exp (-(t/4))`.
* `Talagrand.mass_mul_mass_le_exp_hamming` — the same with the weighted Hamming
  distance: if `∑ w i ^ 2 ≤ 1` and every point of `S` is at weighted Hamming
  distance at least `t` from `A`, then `mass A * mass S ≤ exp (-(t ^ 2 / 4))`.
* `Talagrand.lipschitz_concentration` — the concentration inequality for a
  functional `f` that is 1-Lipschitz for the `w`-weighted Hamming metric:
  `mass {f ≤ m} * mass {f ≥ m + t} ≤ exp (-(t ^ 2 / 4))`.
* `Talagrand.lipschitz_concentration_half` — the usual reading of the previous
  bound when `{f ≤ m}` has mass at least `1/2`.
-/

open Talagrand

open Finset Real

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem Talagrand.mass_mul_mass_le_exp{n : ℕ} {p : Fin n → α → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
    (hp1 : ∀ i, ∑ a, p i a = 1) (A S : Finset (Fin n → α)) {t : ℝ} (hS : ∀ x ∈ S, t ≤ dTsq A x) :
    mass p A * mass p S ≤ Real.exp (-(t / 4)) := by sorry
