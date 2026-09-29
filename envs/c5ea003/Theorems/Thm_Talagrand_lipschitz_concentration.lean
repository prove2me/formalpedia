-- Prove2me | Theorems.Thm_Talagrand_lipschitz_concentration
-- name    : Talagrand.lipschitz_concentration
-- status  : Open
-- author  : @raver1975
-- created : 2026-09-11T00:10:45.139915+00:00
-- url     : https://prove2.me/theorems/5fd2a4fb-78f7-4c9b-bd6a-4c9af963e244
-- title:
--   Concentration of 1-Lipschitz functionals.
-- statement:
--   **Concentration of 1-Lipschitz functionals.**  If `f` is 1-Lipschitz for the
--   `w`-weighted Hamming metric (with `∑ w i ^ 2 ≤ 1`), then the level set `{f ≤ m}`
--   and the far level set `{f ≥ m + t}` cannot both be large.
--
--   ```lean
--   theorem Talagrand.lipschitz_concentration{n : ℕ} {p : Fin n → α → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
--       (hp1 : ∀ i, ∑ a, p i a = 1) {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (hw2 : ∑ i, (w i) ^ 2 ≤ 1)
--       {f : (Fin n → α) → ℝ}
--       (hLip : ∀ x y, f x ≤ f y + ∑ i, w i * hamm (x i) (y i))
--       (A S : Finset (Fin n → α)) (hA : A.Nonempty) {m t : ℝ} (ht : 0 ≤ t)
--       (hAle : ∀ y ∈ A, f y ≤ m) (hSge : ∀ x ∈ S, m + t ≤ f x) :
--       mass p A * mass p S ≤ Real.exp (-(t ^ 2 / 4)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TalagrandConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TalagrandConcentration.lean#L83

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

theorem Talagrand.lipschitz_concentration{n : ℕ} {p : Fin n → α → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
    (hp1 : ∀ i, ∑ a, p i a = 1) {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (hw2 : ∑ i, (w i) ^ 2 ≤ 1)
    {f : (Fin n → α) → ℝ}
    (hLip : ∀ x y, f x ≤ f y + ∑ i, w i * hamm (x i) (y i))
    (A S : Finset (Fin n → α)) (hA : A.Nonempty) {m t : ℝ} (ht : 0 ≤ t)
    (hAle : ∀ y ∈ A, f y ≤ m) (hSge : ∀ x ∈ S, m + t ≤ f x) :
    mass p A * mass p S ≤ Real.exp (-(t ^ 2 / 4)) := by sorry
