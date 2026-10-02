-- Prove2me | solution 1 for BookSixth.canonical_shrunk_circle_is_round
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-28T10:32:53.664235+00:00
-- url     : https://prove2.me/submissions/10861fb5-c6bf-45ac-9af0-4dc68b8dd51e

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

noncomputable section

/-- **`canonical_shrunk_circle_is_round` is false as stated: `s < r` does not
bound `|s|`.**

The hypothesis is only `s < r`, with no lower bound on `s`.  Take `r = 1` and
`s = -1`.  Every hypothesis then holds, but the radicand is
`1 ^ 2 - (-1) ^ 2 = 0`, so the displayed set collapses to the singleton
`{c}`, which is not a round circle: a round circle has strictly positive
radius, and a singleton has none.

The refutation is by membership rather than by rewriting `Set.range`.  If
`{(0 : Space3)} = Set.range (fun t => c + (r * cos t) • u + (r * sin t) • v)`,
then the parameters `0` and `Real.pi` both land in the singleton, so
`c + r • u = c` and `c - r • u = c`.  Subtracting `c` gives `r • u = -r • u`,
hence `r • u = 0`, and `r > 0` together with `‖u‖ = 1` rules that out.

The missing hypothesis is `0 ≤ s`, which is exactly what the sibling
`BookSixth.canonical_shrunk_circle_is_round_nonneg_height` adds; with it the
statement is true and already proved. -/
theorem solution : ¬ (∀ (c u v : Space3) (r : ℝ), 0 < r →
    (∑ i, u i * u i) = 1 → (∑ i, v i * v i) = 1 → (∑ i, u i * v i) = 0 →
    ∀ s : ℝ, s < r →
      RoundCircle (Set.range (fun t : ℝ =>
        c + (Real.sqrt (r ^ 2 - s ^ 2) * Real.cos t) • u
          + (Real.sqrt (r ^ 2 - s ^ 2) * Real.sin t) • v))) := by
  intro h
  -- The orthonormal side conditions hold for the standard frame `e₀, e₁`.
  have key : ∀ s : ℝ, s < 1 →
      RoundCircle (Set.range (fun t : ℝ =>
        (0 : Space3) + (Real.sqrt (1 ^ 2 - s ^ 2) * Real.cos t) • ![1, 0, 0]
          + (Real.sqrt (1 ^ 2 - s ^ 2) * Real.sin t) • ![0, 1, 0])) :=
    fun s hs => h (0 : Space3) ![1, 0, 0] ![0, 1, 0] 1 (by norm_num)
      (by simp [Fin.sum_univ_succ]) (by simp [Fin.sum_univ_succ])
      (by simp [Fin.sum_univ_succ]) s hs
  -- At `s = -1` the radicand is zero, so the range is the singleton `{0}`.
  have hzero : Set.range (fun t : ℝ =>
        (0 : Space3) + (Real.sqrt (1 ^ 2 - (-1) ^ 2) * Real.cos t) • ![1, 0, 0]
          + (Real.sqrt (1 ^ 2 - (-1) ^ 2) * Real.sin t) • ![0, 1, 0]) = {(0 : Space3)} := by
    have hz : Real.sqrt (1 ^ 2 - ((-1 : ℝ)) ^ 2) = 0 := by
      rw [show (1 : ℝ) ^ 2 - ((-1 : ℝ)) ^ 2 = 0 by ring, Real.sqrt_zero]
    simp [hz]
  have hrnd : RoundCircle {(0 : Space3)} := by
    rw [← hzero]
    exact key (-1) (by norm_num)
  -- A round circle contains `c + r • u` (at `t = 0`) and `c - r • u` (at `t = π`).
  -- Both are written in the exact form the range produces, namely
  -- `c + (r * cos t) • u + (r * sin t) • v` reassociated by `add_smul`.
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hC⟩ := hrnd
  -- The two parameters `0` and `π` give the two antipodal points of the circle.
  have hmem0 : c + r • u ∈ Set.range (fun t : ℝ =>
      c + (r * Real.cos t) • u + (r * Real.sin t) • v) :=
    ⟨0, by
      show c + (r * Real.cos 0) • u + (r * Real.sin 0) • v = c + r • u
      simp⟩
  have hmempi : c - r • u ∈ Set.range (fun t : ℝ =>
      c + (r * Real.cos t) • u + (r * Real.sin t) • v) :=
    ⟨Real.pi, by
      show c + (r * Real.cos Real.pi) • u + (r * Real.sin Real.pi) • v = c - r • u
      rw [Real.cos_pi, Real.sin_pi, sub_eq_add_neg]
      -- `sub_eq_add_neg` is definitional (`rfl`), so the right-hand side
      -- `c - r • u` is now `c + -r • u`. The left-hand side still has
      -- `(r * -1) • u` and `(r * 0) • v`. `mul_neg_one` and `neg_smul` reduce
      -- the first to `-(r • u)`; the second is `0 • v`, so it needs
      -- `zero_smul` (`0 • m = 0`), not `smul_zero` (`m • 0 = 0`).
      simp only [mul_neg_one, neg_smul, mul_zero, zero_smul, add_zero]⟩
  -- `hC` already relates the range to the singleton `{(0 : Space3)}`, and
  -- `Set.eq_of_mem_singleton` reads singleton membership off as an equality.
  -- No `{…}` literal is written in a `∈` here: at such a position the literal's
  -- expected type is only `Prop`, so its container is never determined and
  -- typeclass resolution gets stuck on `Singleton Space3 ?m`. Substituting along
  -- `hC` keeps the singleton's type pinned by `hC` itself.
  have h0 : c + r • u = (0 : Space3) := Set.eq_of_mem_singleton (hC ▸ hmem0)
  have hpi : c - r • u = (0 : Space3) := Set.eq_of_mem_singleton (hC ▸ hmempi)
  -- `Space3` is the Pi type `Fin 3 → ℝ`, so `h0` and `hpi` are *pointwise*
  -- equations, not single linear ones. `linarith` sees `c + r • u` and
  -- `c - r • u` as two unrelated opaque atoms and can never combine them.
  -- Applying both at one coordinate makes the atoms `c i` and `r * u i`,
  -- which are genuinely linear in ℝ, and then the subtraction cancels `c i`.
  have hz : ∀ i : Fin 3, u i = 0 := by
    intro i
    have h0i := congrArg (fun f : Space3 => f i) h0
    have hpii := congrArg (fun f : Space3 => f i) hpi
    change c i + r * u i = 0 at h0i
    change c i - r * u i = 0 at hpii
    have hprod : r * u i = 0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_left hr.ne'
  -- The contradiction needs *all* of `u`, not just `u 0`: a unit vector may
  -- well have `u 0 = 0` (take `![0, 1, 0]`), so the unit-norm identity is
  -- contradicted only once the whole vector is zero.
  -- With every coordinate zero the unit-norm sum collapses to `0 = 1`.
  have hz0 : (∑ i, u i * u i) = 0 := by simp [hz]
  rw [hz0] at hu
  norm_num at hu

end
