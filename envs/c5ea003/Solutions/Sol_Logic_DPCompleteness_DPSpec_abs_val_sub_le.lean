-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.abs_val_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:00:58.012282+00:00
-- url     : https://prove2.me/submissions/d3f7bc92-eae1-4907-aca8-f8cc09cd1de8

-- Sol generated from Logic/DPCompletenessStability.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessStability
import Theorems.Thm_Logic_DPCompleteness_DPSpec_val_mono
import Theorems.Thm_Logic_DPCompleteness_DPSpec_val_shift
/-
# Stability of the DP value function under perturbation of the specification

The completeness theorem of `Logic.DPCompleteness` says the DP value is the exact optimum over
all labellings.  This file quantifies how that optimum reacts to perturbing the data.

* `DPSpec.shift` uniformly shifts the initial weights by `a` and every transition weight by `b`;
  `DPSpec.val_shift` shows the value function shifts by exactly `a + n • b` — the DP optimum is
  *equivariant* for the additive action of constants.
* `DPSpec.abs_val_sub_le` is the resulting Lipschitz stability bound: if two specifications
  differ by at most `a` on initial weights and at most `b` on transition weights, their value
  functions differ by at most `a + n • b` at horizon `n`.
* `DPSpec.near_optimal_transfer` turns this into a robustness statement about *runs*: a DP run
  computed for a perturbed model is within `2 • (a + n • b)` of the true optimum.  Combined with
  completeness this says the DP is not merely exact, but *stably* exact.

The weight monoid here is a linearly ordered additive commutative group (e.g. `ℤ`, `ℚ`, `ℝ`).
-/


open Logic.DPCompleteness

open DPSpec


variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]







variable {S W : Type*} [AddCommGroup W] [Fintype S] [Nonempty S] [LinearOrder W]
  [IsOrderedAddMonoid W]

omit [Fintype S] [Nonempty S] in
/-- From a two-sided bound `|x - y| ≤ c` we extract `x ≤ y + c`. -/
theorem le_add_of_abs_sub_le {x y c : W} (h : |x - y| ≤ c) : x ≤ y + c :=
  sub_le_iff_le_add'.mp (abs_le.mp h).2

/-- Comparison of value functions from a one-sided comparison of specifications. -/
theorem val_le_val_shift {D D' : DPSpec S W} {a b : W}
    (hinit : ∀ s, D'.init s ≤ D.init s + a) (hstep : ∀ i s t, D'.step i s t ≤ D.step i s t + b) :
    ∀ (n : ℕ) (s : S), D'.val n s ≤ D.val n s + (a + n • b) := by
  intro n s
  have h := val_mono (D := D') (D' := D.shift a b) hinit hstep n s
  rwa [val_shift] at h








open Logic.DPCompleteness in
theorem solution{D D' : DPSpec S W} {a b : W}
    (hinit : ∀ s, |D'.init s - D.init s| ≤ a) (hstep : ∀ i s t, |D'.step i s t - D.step i s t| ≤ b)
    (n : ℕ) (s : S) : |D'.val n s - D.val n s| ≤ a + n • b := by
  have hi1 : ∀ s, D'.init s ≤ D.init s + a := fun s => le_add_of_abs_sub_le (hinit s)
  have hi2 : ∀ s, D.init s ≤ D'.init s + a := fun s =>
    le_add_of_abs_sub_le (by rw [abs_sub_comm]; exact hinit s)
  have hs1 : ∀ i s t, D'.step i s t ≤ D.step i s t + b :=
    fun i s t => le_add_of_abs_sub_le (hstep i s t)
  have hs2 : ∀ i s t, D.step i s t ≤ D'.step i s t + b := fun i s t =>
    le_add_of_abs_sub_le (by rw [abs_sub_comm]; exact hstep i s t)
  have h1 := val_le_val_shift hi1 hs1 n s
  have h2 := val_le_val_shift hi2 hs2 n s
  rw [abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add'.mpr h1, sub_le_iff_le_add'.mpr h2⟩
