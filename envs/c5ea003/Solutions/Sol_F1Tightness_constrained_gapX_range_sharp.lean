-- Prove2me | solution 1 for F1Tightness.constrained_gapX_range_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:45:34.491785+00:00
-- url     : https://prove2.me/submissions/772fa7c4-5866-4284-b135-562541d2e46b

-- Sol generated from Probability/F1TightnessPolytope.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration
import Definitions.Def_Probability_F1TightnessPolytope
import Theorems.Thm_F1Tightness_deltaLast_gapX
import Theorems.Thm_F1Tightness_gapX_le_of_edgeMass
import Theorems.Thm_F1Tightness_gapX_mem_Icc
import Theorems.Thm_F1Tightness_pairProfile_edgeMass
import Theorems.Thm_F1Tightness_pairProfile_gapX_extremal

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










open F1Tightness in
theorem solution{K : ℕ} {m : ℝ} (hM : 0 < M) (hK : 0 < K)
    (hKM : K < M) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    (∀ p : Fin M → ℝ, (∀ i, 0 ≤ p i) → (∑ i : Fin M, p i = 1) → m ≤ edgeMass K p →
        ((M : ℝ) + 1) / (2 * (M : ℝ)) ≤ gapX p
          ∧ gapX p ≤ ((M : ℝ) + 1) / (2 * (K : ℝ) * m + 2))
      ∧ (edgeMass K (pairProfile (⟨0, hM⟩ : Fin M) (⟨K, hKM⟩ : Fin M) m) = m
          ∧ gapX (pairProfile (⟨0, hM⟩ : Fin M) (⟨K, hKM⟩ : Fin M) m)
              = ((M : ℝ) + 1) / (2 * (K : ℝ) * m + 2))
      ∧ (m ≤ edgeMass K (deltaLast M)
          ∧ gapX (deltaLast M) = ((M : ℝ) + 1) / (2 * (M : ℝ))) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp hsum hm
    exact ⟨(gapX_mem_Icc hM hp hsum).1, gapX_le_of_edgeMass hM h0 hp hsum hm⟩
  · exact pairProfile_edgeMass (by simp [hK]) (by simp)
  · exact pairProfile_gapX_extremal hM hKM h0 h1
  · have hlast : edgeMass K (deltaLast M) = 1 := by
      unfold edgeMass deltaLast
      have h : ∀ i : Fin M, (if ((i : ℕ) = M - 1) then (1 : ℝ) else 0)
          = (if i = (⟨M - 1, by omega⟩ : Fin M) then (1 : ℝ) else 0) := by
        intro i
        simp [Fin.ext_iff]
      rw [Finset.sum_congr rfl fun i _ => h i,
        Finset.sum_ite_eq' _ (⟨M - 1, by omega⟩ : Fin M)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_pos (by omega)]
    rw [hlast]
    exact h1
  · exact deltaLast_gapX hM
