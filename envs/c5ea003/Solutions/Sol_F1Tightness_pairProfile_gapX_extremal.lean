-- Prove2me | solution 1 for F1Tightness.pairProfile_gapX_extremal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:40:46.95727+00:00
-- url     : https://prove2.me/submissions/443c0d60-b654-4b29-8e34-e6108f8a8b57

-- Sol generated from Probability/F1TightnessPolytope.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration
import Definitions.Def_Probability_F1TightnessPolytope
import Theorems.Thm_F1Tightness_gapX_eq_meanPos

/-!
# The constrained mean-position polytope of the slack factor

`Probability.F1TightnessFibration` solved the *unconstrained* extremal problem
for the slack factor `X`: since `X` depends on the profile only through the mean
probe position `E_x`, and the reachable mean positions form the interval
`[1/(2M), (2M−1)/(2M)]`, the reachable slacks are exactly
`[(M+1)/(2M), (M+1)/2]`.

Direction 3 of `FUTURE_DIRECTIONS.md` asks for the same computation under the
measured *tail* constraint: the profile must place at least a mass `m` on the
cells from index `K` on (the "edge mass bounded below" constraint of the
measured positional profile).  This file closes that question for a single
linear tail constraint.

* `edgeMass` — the mass on the cells of index `≥ K`.
* `meanPos_ge_of_edgeMass` — the sharp linear-programming bound
  `E_x ≥ (1/2 + K·m)/M` for every admissible profile.
* `gapX_le_of_edgeMass` — the resulting constraint on the slack,
  `X ≤ (M+1)/(2·K·m + 2)`.
* `pairProfile` — the two-cell profile `(1−m)·δ_a + m·δ_b`; the bound above is
  attained by `pairProfile 0 K m`, so the extremal profile of the constrained
  linear programme is supported on **at most two cells**, as conjectured.
* `constrained_gapX_range_sharp` — the packaged statement: under the tail
  constraint the reachable slacks are exactly `[(M+1)/(2M), (M+1)/(2·K·m+2)]`,
  both endpoints attained.
* `edgeMass_bound_of_gapX` — read backwards, a *measured* slack bounds the
  admissible edge mass: `K·m ≤ ((M+1)/X − 2)/2`.  This is the promised transfer
  of the booked CI on `Λ` into a constraint on the prior itself.
-/

open F1Tightness

open Finset

variable {M : ℕ}





/-! ## Attainment by a two-cell profile -/


theorem pairProfile_nonneg {a b : Fin M} {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    ∀ i, 0 ≤ pairProfile a b m i := by
  intro i
  unfold pairProfile
  have h₁ : (0 : ℝ) ≤ if i = a then 1 - m else 0 := by
    split <;> linarith
  have h₂ : (0 : ℝ) ≤ if i = b then m else 0 := by
    split <;> linarith
  linarith

theorem pairProfile_sum (a b : Fin M) (m : ℝ) :
    ∑ i : Fin M, pairProfile a b m i = 1 := by
  unfold pairProfile
  rw [Finset.sum_add_distrib]
  simp

theorem pairProfile_meanPos (a b : Fin M) (m : ℝ) :
    meanPos (pairProfile a b m)
      = ((((a : ℕ) : ℝ) + 1 / 2) / (M : ℝ)) * (1 - m)
        + ((((b : ℕ) : ℝ) + 1 / 2) / (M : ℝ)) * m := by
  unfold meanPos pairProfile
  have h : ∀ i : Fin M,
      ((((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ))
          * ((if i = a then 1 - m else 0) + (if i = b then m else 0))
        = (if i = a then ((((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ)) * (1 - m) else 0)
          + (if i = b then ((((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ)) * m else 0) := by
    intro i
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
  simp






open F1Tightness in
theorem solution{K : ℕ} {m : ℝ} (hM : 0 < M)
    (hKM : K < M) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    gapX (pairProfile (⟨0, hM⟩ : Fin M) (⟨K, hKM⟩ : Fin M) m)
      = ((M : ℝ) + 1) / (2 * (K : ℝ) * m + 2) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hmean : meanPos (pairProfile (⟨0, hM⟩ : Fin M) (⟨K, hKM⟩ : Fin M) m)
      = (1 / 2 + (K : ℝ) * m) / (M : ℝ) := by
    rw [pairProfile_meanPos]
    field_simp
    ring
  rw [gapX_eq_meanPos hM (pairProfile_nonneg h0 h1) (pairProfile_sum _ _ m), hmean]
  have hden : 2 * (M : ℝ) * ((1 / 2 + (K : ℝ) * m) / (M : ℝ)) + 1
      = 2 * (K : ℝ) * m + 2 := by
    field_simp
    ring
  rw [hden]
