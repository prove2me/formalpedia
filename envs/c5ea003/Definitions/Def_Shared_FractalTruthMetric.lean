-- Prove2me | Definitions.Def_Shared_FractalTruthMetric
-- name    : Shared_FractalTruthMetric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:52.489498+00:00
-- url     : https://prove2.me/theorems/56057ad9-4a4b-41ba-adc3-0c203ecb9215
-- title:
--   Aether Catalog definitions — Shared_FractalTruthMetric
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.FractalTruthMetric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/FractalTruthMetric.lean by skeleton subtraction
import Mathlib

/-!
# The Cantor first-disagreement ultrametric on the truth space

A mathematical statement is represented by its truth value, and an infinite theory by a binary
stream `x : ℕ → Bool`.  The previous cycle (`FractalTruth.lean`) studied the golden-mean
*cylinder* combinatorics of such streams: the number of admissible depth-`n` patterns is
`fib (n+2)`, giving box dimension `log φ / log 2`.

This file supplies **natural next step #1**: the actual Cantor ultrametric coming from the first
index of disagreement, its metric axioms (including the strong / ultrametric triangle
inequality), and the exact identification of radius-`2⁻ⁿ` closed balls with the prefix-agreement
relation `AgreeTo n`.  This is the metric bridge underlying the box-dimension picture.

The development is a self-contained chain: each result feeds the next, culminating in

* `cantorDist_le_iff_agreeTo` — closed balls of radius `2⁻ⁿ` are exactly the agreement classes,
* `cantorDist_ultra` — the ultrametric (strong triangle) inequality,

which together upgrade the truth space to a genuine `MetricSpace` on the Cantor type synonym.
-/

namespace FractalTruthMetric

open Classical

/-! ## Prefix agreement -/

/-- Prefix agreement: `x` and `y` give the same first `n` answers. -/
def AgreeTo (n : ℕ) (x y : ℕ → Bool) : Prop := ∀ k < n, x k = y k



theorem agreeTo_trans {n : ℕ} {x y z : ℕ → Bool}
    (hxy : AgreeTo n x y) (hyz : AgreeTo n y z) : AgreeTo n x z :=
  fun k hk => (hxy k hk).trans (hyz k hk)



/-! ## The first index of disagreement -/

/-- The least index at which two streams disagree (`0` by convention if they are equal). -/
noncomputable def firstDiff (x y : ℕ → Bool) : ℕ := sInf {k | x k ≠ y k}

/-- Distinct streams differ somewhere. -/
theorem exists_diff_of_ne {x y : ℕ → Bool} (h : x ≠ y) : ∃ k, x k ≠ y k := by
  by_contra hc; push_neg at hc; exact h (funext hc)

/-- The streams genuinely disagree at their first point of disagreement. -/
theorem firstDiff_spec {x y : ℕ → Bool} (h : x ≠ y) :
    x (firstDiff x y) ≠ y (firstDiff x y) :=
  Nat.sInf_mem (exists_diff_of_ne h)

/-- The two streams agree strictly before the first disagreement. -/
theorem agreeTo_firstDiff (x y : ℕ → Bool) : AgreeTo (firstDiff x y) x y := by
  intro k hk; by_contra hc
  exact absurd (Nat.sInf_le (show k ∈ {k | x k ≠ y k} from hc)) (not_le.mpr hk)

/-- `firstDiff` is symmetric. -/
theorem firstDiff_comm (x y : ℕ → Bool) : firstDiff x y = firstDiff y x := by
  unfold firstDiff; congr 1; ext k; exact ne_comm

/-- For distinct streams, prefix agreement to depth `n` is exactly `n ≤ firstDiff`. -/
theorem agreeTo_iff_le_firstDiff {x y : ℕ → Bool} (h : x ≠ y) {n : ℕ} :
    AgreeTo n x y ↔ n ≤ firstDiff x y := by
  constructor
  · intro hA; by_contra hlt; push_neg at hlt; exact firstDiff_spec h (hA _ hlt)
  · intro hle k hk; exact (agreeTo_firstDiff x y) k (lt_of_lt_of_le hk hle)

/-! ## The Cantor distance -/

/-- The Cantor first-disagreement distance. -/
noncomputable def cantorDist (x y : ℕ → Bool) : ℝ :=
  if x = y then 0 else (2 : ℝ) ^ (-(firstDiff x y : ℤ))

theorem cantorDist_self (x : ℕ → Bool) : cantorDist x x = 0 := by
  simp [cantorDist]

theorem cantorDist_nonneg (x y : ℕ → Bool) : 0 ≤ cantorDist x y := by
  unfold cantorDist
  split
  · rfl
  · positivity

/-- The distance is positive on distinct points. -/
theorem cantorDist_pos_of_ne {x y : ℕ → Bool} (h : x ≠ y) : 0 < cantorDist x y := by
  unfold cantorDist; rw [if_neg h]; positivity

theorem cantorDist_comm (x y : ℕ → Bool) : cantorDist x y = cantorDist y x := by
  unfold cantorDist
  by_cases h : x = y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), firstDiff_comm]

/-- Vanishing distance forces equality. -/
theorem eq_of_cantorDist_eq_zero {x y : ℕ → Bool} (h : cantorDist x y = 0) : x = y := by
  by_contra hne
  exact absurd h (ne_of_gt (cantorDist_pos_of_ne hne))

/-- **Balls are agreement classes**: the closed ball of radius `2⁻ⁿ` about `x` is exactly the set
of streams agreeing with `x` on the first `n` coordinates. -/
theorem cantorDist_le_iff_agreeTo (x y : ℕ → Bool) (n : ℕ) :
    cantorDist x y ≤ (2 : ℝ) ^ (-(n : ℤ)) ↔ AgreeTo n x y := by
  unfold cantorDist
  by_cases h : x = y
  · subst h
    rw [if_pos rfl]
    constructor
    · intro _ k _; rfl
    · intro _; positivity
  · rw [if_neg h, agreeTo_iff_le_firstDiff h,
      zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
    constructor
    · intro hle; exact_mod_cast (neg_le_neg_iff.mp hle)
    · intro hle; exact neg_le_neg (by exact_mod_cast hle)

/-- **Ultrametric (strong triangle) inequality.** -/
theorem cantorDist_ultra (x y z : ℕ → Bool) :
    cantorDist x z ≤ max (cantorDist x y) (cantorDist y z) := by
  by_cases hxz : x = z
  · rw [hxz]; simp only [cantorDist_self]
    exact le_max_of_le_left (cantorDist_nonneg z y)
  by_cases hxy : x = y
  · subst hxy; exact le_max_right _ _
  by_cases hyz : y = z
  · subst hyz; exact le_max_left _ _
  set p := firstDiff x y with hp
  set q := firstDiff y z with hq
  set n := min p q with hn
  have hAxy : AgreeTo n x y :=
    (agreeTo_iff_le_firstDiff hxy).mpr (by rw [hn]; exact min_le_left _ _)
  have hAyz : AgreeTo n y z :=
    (agreeTo_iff_le_firstDiff hyz).mpr (by rw [hn]; exact min_le_right _ _)
  have hAxz : AgreeTo n x z := agreeTo_trans hAxy hAyz
  have h1 : cantorDist x z ≤ (2 : ℝ) ^ (-(n : ℤ)) := (cantorDist_le_iff_agreeTo x z n).mpr hAxz
  have h2 : (2 : ℝ) ^ (-(n : ℤ)) ≤ max (cantorDist x y) (cantorDist y z) := by
    rw [cantorDist, if_neg hxy, cantorDist, if_neg hyz, ← hp, ← hq]
    rcases le_total p q with hpq | hpq
    · have : n = p := by rw [hn]; exact min_eq_left hpq
      rw [this]; exact le_max_left _ _
    · have : n = q := by rw [hn]; exact min_eq_right hpq
      rw [this]; exact le_max_right _ _
  exact h1.trans h2

/-- Ordinary triangle inequality, a consequence of the ultrametric one. -/
theorem cantorDist_triangle (x y z : ℕ → Bool) :
    cantorDist x z ≤ cantorDist x y + cantorDist y z := by
  have h := cantorDist_ultra x y z
  have h3 := cantorDist_nonneg x y
  have h4 := cantorDist_nonneg y z
  rcases le_total (cantorDist x y) (cantorDist y z) with h' | h'
  · rw [max_eq_right h'] at h; linarith
  · rw [max_eq_left h'] at h; linarith

/-! ## The metric space -/

/-- A Cantor-space type synonym carrying the first-disagreement metric. -/
def Cantor : Type := ℕ → Bool

/-- The first-disagreement metric makes the truth space a genuine metric space. -/
noncomputable instance : MetricSpace Cantor where
  dist x y := cantorDist x y
  dist_self x := cantorDist_self x
  dist_comm x y := cantorDist_comm x y
  dist_triangle x y z := cantorDist_triangle x y z
  eq_of_dist_eq_zero h := eq_of_cantorDist_eq_zero h

end FractalTruthMetric


