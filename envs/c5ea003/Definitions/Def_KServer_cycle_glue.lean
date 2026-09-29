-- Prove2me | Definitions.Def_KServer_cycle_glue
-- name    : KServer_cycle_glue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T09:15:24.086261+00:00
-- url     : https://prove2.me/theorems/d7ca7f11-1408-451f-b75b-fe102efd5146
-- title:
--   Cyclic gluing of a metric space along marked points
-- statement:
--   The **cyclic gluing** of a metric space: given a metric space $X$ with two marked points $s, t$, the space $\mathrm{Cycle}_n(X)$ arranges $n$ copies of $X$ in a cycle, identifying the point $t$ of each copy with the point $s$ of the next. Representatives are pairs $(i, x)$ with $i \in \mathbb{Z}/n$ and $x \in X \setminus \{t\}$.
--
--   The metric is defined through the ℤ-indexed **chain** of copies (the universal cover): the chain distance between copies $i < j$ is
--   $$d\bigl((i,x),(j,y)\bigr) \;=\; d(x,t) \;+\; (j-i-1)\,d(s,t) \;+\; d(s,y),$$
--   and the cycle distance is the minimum over the two relevant lifts (the two ways around). The chain distance satisfies the triangle inequality with **no hypotheses on $X$** (a thirteen-case verification using only the triangle inequality of $X$), it is translation invariant, and its value is monotone in the winding number (`cycleDist_le_lift`), which yields the triangle inequality, symmetry and separation of the cycle distance; `cycleMetric` packages the metric space structure.
--
--   Convenience layer: `cyclePt i x` embeds the $i$-th copy, isometrically within a copy (`cycleDist_same`), and across copies the distance is the better of the two ways around (`cycleDist_cross`):
--   $$d\bigl((i,x),(j,y)\bigr) = \min\bigl(d(x,t) + (a-1)D + d(s,y),\; d(x,s) + (n-a-1)D + d(t,y)\bigr),$$
--   with $a = j - i \bmod n$ and $D = d(s,t)$. The space is finite with $n(|X|-1)$ points when $X$ is finite (`card_cyclePoint`).
--
--   ## Role
--
--   This is the construction step of the Bubeck–Coester–Rabani metric spaces (STOC 2023, Section 4): their space $\mathcal{M}_{w+1}$ is the cycle of **six** copies of $\mathcal{M}_w$, viewed as a left and a right path of three copies each between the antipodal junctions. The explicit two-routes distance formula is what the chunked lower-bound induction manipulates.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 4 (the six-copy cycle construction), formalized as a general n-copy cyclic gluing.

import Mathlib

namespace KServer

/-! ### Cyclic gluing of a metric space

`CyclePoint X t n` is the vertex set of the space obtained by arranging `n` copies of
`X` in a cycle, gluing the point `t` of each copy to the point `s` of the next.
Representatives: each copy contributes `X` minus its `t` (which lives on as the next
copy's `s`).

The distance is defined through the ℤ-indexed *chain* of copies (the universal cover):
`chainDist` gives the distance between points of copies `i` and `j` of the infinite
chain, and the cycle distance is the minimum over the two relevant lifts. -/

variable {X : Type*} [MetricSpace X]

/-- Distance in the ℤ-indexed chain of copies of `X`, where each copy's `t` is glued
to the next copy's `s`: moving forward exits a copy at `t` and enters at `s`. -/
noncomputable def chainDist (s t : X) (i : ℤ) (x : X) (j : ℤ) (y : X) : ℝ :=
  if i = j then dist x y
  else if i < j then dist x t + ((j - i - 1 : ℤ) : ℝ) * dist s t + dist s y
  else dist x s + ((i - j - 1 : ℤ) : ℝ) * dist s t + dist t y

theorem chainDist_nonneg (s t : X) (i : ℤ) (x : X) (j : ℤ) (y : X) :
    0 ≤ chainDist s t i x j y := by
  unfold chainDist
  split_ifs with h1 h2
  · exact dist_nonneg
  · have hm : (0 : ℝ) ≤ ((j - i - 1 : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ j - i - 1 := by omega
      exact_mod_cast this
    have := mul_nonneg hm (dist_nonneg (x := s) (y := t))
    have := dist_nonneg (x := x) (y := t)
    have := dist_nonneg (x := s) (y := y)
    linarith
  · have hm : (0 : ℝ) ≤ ((i - j - 1 : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ i - j - 1 := by omega
      exact_mod_cast this
    have := mul_nonneg hm (dist_nonneg (x := s) (y := t))
    have := dist_nonneg (x := x) (y := s)
    have := dist_nonneg (x := t) (y := y)
    linarith

theorem chainDist_comm (s t : X) (i : ℤ) (x : X) (j : ℤ) (y : X) :
    chainDist s t i x j y = chainDist s t j y i x := by
  unfold chainDist
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega)]
    rw [dist_comm x t, dist_comm s y]
    ring
  · rw [if_pos h, if_pos h.symm, dist_comm]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
    rw [dist_comm x s, dist_comm t y]
    ring

theorem chainDist_shift (s t : X) (i : ℤ) (x : X) (j : ℤ) (y : X) (m : ℤ) :
    chainDist s t (i + m) x (j + m) y = chainDist s t i x j y := by
  unfold chainDist
  have h1 : (i + m = j + m) ↔ (i = j) := by omega
  have h2 : (i + m < j + m) ↔ (i < j) := by omega
  have h3 : (j + m - (i + m) - 1 : ℤ) = j - i - 1 := by ring
  have h4 : (i + m - (j + m) - 1 : ℤ) = i - j - 1 := by ring
  by_cases he : i = j
  · rw [if_pos (h1.mpr he), if_pos he]
  · rw [if_neg (fun hc => he (h1.mp hc)), if_neg he]
    by_cases hl : i < j
    · rw [if_pos (h2.mpr hl), if_pos hl, h3]
    · rw [if_neg (fun hc => hl (h2.mp hc)), if_neg hl, h4]

/-- The chain triangle inequality. -/
theorem chainDist_triangle (s t : X) (i : ℤ) (x : X) (j : ℤ) (y : X) (k : ℤ) (z : X) :
    chainDist s t i x k z ≤ chainDist s t i x j y + chainDist s t j y k z := by
  have hD : (0 : ℝ) ≤ dist s t := dist_nonneg
  have hcast : ∀ a b : ℤ, a ≤ b → ((a : ℝ) : ℝ) * dist s t ≤ ((b : ℝ)) * dist s t := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hD
  unfold chainDist
  rcases lt_trichotomy i j with hij | hij | hij <;>
    rcases lt_trichotomy j k with hjk | hjk | hjk <;>
    rcases lt_trichotomy i k with hik | hik | hik <;>
    try omega
  -- i < j, j < k, i < k
  · rw [if_neg (by omega : ¬ i = k), if_pos hik, if_neg (by omega : ¬ i = j), if_pos hij,
      if_neg (by omega : ¬ j = k), if_pos hjk]
    have h1 : dist s t ≤ dist s y + dist y t := dist_triangle s y t
    have h2 : ((k - i - 1 : ℤ) : ℝ) = ((j - i - 1 : ℤ) : ℝ) + ((k - j - 1 : ℤ) : ℝ) + 1 := by
      push_cast; ring
    rw [h2]
    have h3 : (((j - i - 1 : ℤ) : ℝ) + ((k - j - 1 : ℤ) : ℝ) + 1) * dist s t
        = ((j - i - 1 : ℤ) : ℝ) * dist s t + ((k - j - 1 : ℤ) : ℝ) * dist s t + dist s t := by
      ring
    rw [h3]
    linarith
  -- i < j, j < k contradictions handled by omega; next: i < j, j = k
  · rw [if_neg (by omega : ¬ i = k), if_pos hik, if_neg (by omega : ¬ i = j), if_pos hij,
      if_pos hjk]
    have h1 : dist s z ≤ dist s y + dist y z := dist_triangle s y z
    have h2 : (k - i - 1 : ℤ) = j - i - 1 := by omega
    rw [h2]
    linarith
  -- i < j, k < j, i < k
  · rw [if_neg (by omega : ¬ i = k), if_pos hik, if_neg (by omega : ¬ i = j), if_pos hij,
      if_neg (by omega : ¬ j = k), if_neg (by omega : ¬ j < k)]
    have h1 : dist s z ≤ dist s t + dist t z := dist_triangle s t z
    have h2 : ((k - i - 1 : ℤ) : ℝ) + 1 ≤ ((j - i - 1 : ℤ) : ℝ) + ((j - k - 1 : ℤ) : ℝ) := by
      have : (k - i - 1 : ℤ) + 1 ≤ (j - i - 1) + (j - k - 1) := by omega
      exact_mod_cast this
    have h3 := mul_le_mul_of_nonneg_right h2 hD
    have h4 : (((k - i - 1 : ℤ) : ℝ) + 1) * dist s t
        = ((k - i - 1 : ℤ) : ℝ) * dist s t + dist s t := by ring
    have h5 : (((j - i - 1 : ℤ) : ℝ) + ((j - k - 1 : ℤ) : ℝ)) * dist s t
        = ((j - i - 1 : ℤ) : ℝ) * dist s t + ((j - k - 1 : ℤ) : ℝ) * dist s t := by ring
    rw [h4, h5] at h3
    linarith [dist_nonneg (x := s) (y := y), dist_nonneg (x := y) (y := s)]
  -- i < j, k < j, i = k
  · rw [if_pos hik, if_neg (by omega : ¬ i = j), if_pos hij,
      if_neg (by omega : ¬ j = k), if_neg (by omega : ¬ j < k)]
    have h1 : dist x z ≤ dist x t + dist t z := dist_triangle x t z
    have h2 := hcast 0 (j - i - 1) (by omega)
    have h3 := hcast 0 (j - k - 1) (by omega)
    simp only [Int.cast_zero, zero_mul] at h2 h3
    nlinarith [dist_nonneg (x := s) (y := y), dist_nonneg (x := y) (y := s)]
  -- i < j, k < j, k < i
  · rw [if_neg (by omega : ¬ i = k), if_neg (by omega : ¬ i < k),
      if_neg (by omega : ¬ i = j), if_pos hij,
      if_neg (by omega : ¬ j = k), if_neg (by omega : ¬ j < k)]
    have h1 : dist x s ≤ dist x t + dist s t := by
      have h := dist_triangle x t s
      have h' : dist t s = dist s t := dist_comm t s
      linarith
    have h2 : ((i - k - 1 : ℤ) : ℝ) + 1 ≤ ((j - i - 1 : ℤ) : ℝ) + ((j - k - 1 : ℤ) : ℝ) := by
      have : (i - k - 1 : ℤ) + 1 ≤ (j - i - 1) + (j - k - 1) := by omega
      exact_mod_cast this
    have h3 := mul_le_mul_of_nonneg_right h2 hD
    have h4 : (((i - k - 1 : ℤ) : ℝ) + 1) * dist s t
        = ((i - k - 1 : ℤ) : ℝ) * dist s t + dist s t := by ring
    have h5 : (((j - i - 1 : ℤ) : ℝ) + ((j - k - 1 : ℤ) : ℝ)) * dist s t
        = ((j - i - 1 : ℤ) : ℝ) * dist s t + ((j - k - 1 : ℤ) : ℝ) * dist s t := by ring
    rw [h4, h5] at h3
    linarith [dist_nonneg (x := s) (y := y), dist_nonneg (x := y) (y := s)]
  -- i = j cases
  · rw [if_neg (by omega : ¬ i = k), if_pos hik, if_pos hij,
      if_neg (by omega : ¬ j = k), if_pos hjk]
    have h1 : dist x t ≤ dist x y + dist y t := dist_triangle x y t
    have h2 : (k - i - 1 : ℤ) = k - j - 1 := by omega
    rw [h2]
    linarith
  · rw [if_pos hik, if_pos hij, if_pos hjk]
    exact dist_triangle x y z
  · rw [if_neg (by omega : ¬ i = k), if_neg (by omega : ¬ i < k), if_pos hij,
      if_neg (by omega : ¬ j = k), if_neg (by omega : ¬ j < k)]
    have h1 : dist x s ≤ dist x y + dist y s := dist_triangle x y s
    have h2 : (i - k - 1 : ℤ) = j - k - 1 := by omega
    rw [h2]
    linarith
  -- j < i cases
  · rw [if_neg (by omega : ¬ i = k), if_pos hik,
      if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ i < j),
      if_neg (by omega : ¬ j = k), if_pos hjk]
    have h1 : dist x t ≤ dist x s + dist s t := dist_triangle x s t
    have h2 : ((k - i - 1 : ℤ) : ℝ) + 1 ≤ ((i - j - 1 : ℤ) : ℝ) + ((k - j - 1 : ℤ) : ℝ) := by
      have : (k - i - 1 : ℤ) + 1 ≤ (i - j - 1) + (k - j - 1) := by omega
      exact_mod_cast this
    have h3 := mul_le_mul_of_nonneg_right h2 hD
    have h4 : (((k - i - 1 : ℤ) : ℝ) + 1) * dist s t
        = ((k - i - 1 : ℤ) : ℝ) * dist s t + dist s t := by ring
    have h5 : (((i - j - 1 : ℤ) : ℝ) + ((k - j - 1 : ℤ) : ℝ)) * dist s t
        = ((i - j - 1 : ℤ) : ℝ) * dist s t + ((k - j - 1 : ℤ) : ℝ) * dist s t := by ring
    rw [h4, h5] at h3
    linarith [dist_nonneg (x := t) (y := y), dist_nonneg (x := y) (y := t)]
  · rw [if_pos hik, if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ i < j),
      if_neg (by omega : ¬ j = k), if_pos hjk]
    have h1 : dist x z ≤ dist x s + dist s z := dist_triangle x s z
    have h2 := hcast 0 (i - j - 1) (by omega)
    have h3 := hcast 0 (k - j - 1) (by omega)
    simp only [Int.cast_zero, zero_mul] at h2 h3
    nlinarith [dist_nonneg (x := t) (y := y), dist_nonneg (x := y) (y := t)]
  · -- j < i, j < k, k < i
    rw [if_neg (by omega : ¬ i = k), if_neg (by omega : ¬ i < k),
      if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ i < j),
      if_neg (by omega : ¬ j = k), if_pos hjk]
    have h1 : dist t z ≤ dist s t + dist s z := by
      have h := dist_triangle t s z
      have h' : dist t s = dist s t := dist_comm t s
      linarith
    have h2 : ((i - k - 1 : ℤ) : ℝ) + 1 ≤ ((i - j - 1 : ℤ) : ℝ) + ((k - j - 1 : ℤ) : ℝ) := by
      have : (i - k - 1 : ℤ) + 1 ≤ (i - j - 1) + (k - j - 1) := by omega
      exact_mod_cast this
    have h3 := mul_le_mul_of_nonneg_right h2 hD
    have h4 : (((i - k - 1 : ℤ) : ℝ) + 1) * dist s t
        = ((i - k - 1 : ℤ) : ℝ) * dist s t + dist s t := by ring
    have h5 : (((i - j - 1 : ℤ) : ℝ) + ((k - j - 1 : ℤ) : ℝ)) * dist s t
        = ((i - j - 1 : ℤ) : ℝ) * dist s t + ((k - j - 1 : ℤ) : ℝ) * dist s t := by ring
    rw [h4, h5] at h3
    linarith [dist_nonneg (x := t) (y := y), dist_nonneg (x := y) (y := t)]
  · -- j < i, j = k, k < i
    rw [if_neg (by omega : ¬ i = k), if_neg (by omega : ¬ i < k),
      if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ i < j),
      if_pos hjk]
    have h1 : dist t z ≤ dist t y + dist y z := dist_triangle t y z
    have h2 : (i - k - 1 : ℤ) = i - j - 1 := by omega
    rw [h2]
    linarith
  · -- j < i, k < j, k < i
    rw [if_neg (by omega : ¬ i = k), if_neg (by omega : ¬ i < k),
      if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ i < j),
      if_neg (by omega : ¬ j = k), if_neg (by omega : ¬ j < k)]
    have h1 : dist s t ≤ dist t y + dist y s := by
      have h := dist_triangle t y s
      have h' : dist s t = dist t s := dist_comm s t
      linarith
    have h2 : ((i - k - 1 : ℤ) : ℝ) = ((i - j - 1 : ℤ) : ℝ) + ((j - k - 1 : ℤ) : ℝ) + 1 := by
      push_cast; ring
    rw [h2]
    have h3 : (((i - j - 1 : ℤ) : ℝ) + ((j - k - 1 : ℤ) : ℝ) + 1) * dist s t
        = ((i - j - 1 : ℤ) : ℝ) * dist s t + ((j - k - 1 : ℤ) : ℝ) * dist s t + dist s t := by
      ring
    rw [h3]
    linarith

/-! ### The cycle of `n` copies -/

/-- The vertex set of the cycle of `n` copies of `X`: each copy contributes `X`
minus its `t`, which is identified with the next copy's `s`. -/
def CyclePoint (X : Type*) (t : X) (n : ℕ) : Type _ := Fin n × {x : X // x ≠ t}

/-- The forward lift: the ℤ-chain index, at or ahead of `p`'s copy, representing
`q`'s copy. -/
def fwdLift {X : Type*} {t : X} {n : ℕ} (p q : CyclePoint X t n) : ℤ :=
  (p.1.val : ℤ) + ((q.1 - p.1 : Fin n).val : ℤ)

theorem fwdLift_ge {X : Type*} {t : X} {n : ℕ} (p q : CyclePoint X t n) :
    (p.1.val : ℤ) ≤ fwdLift p q := by
  unfold fwdLift
  have : (0 : ℤ) ≤ ((q.1 - p.1 : Fin n).val : ℤ) := by positivity
  omega

theorem fwdLift_lt {X : Type*} {t : X} {n : ℕ} (p q : CyclePoint X t n) :
    fwdLift p q < (p.1.val : ℤ) + n := by
  unfold fwdLift
  have : ((q.1 - p.1 : Fin n).val : ℤ) < n := by exact_mod_cast (q.1 - p.1).isLt
  omega

theorem fwdLift_split {X : Type*} {t : X} {n : ℕ} [NeZero n] (p q : CyclePoint X t n) :
    fwdLift p q = (q.1.val : ℤ) ∨ fwdLift p q = (q.1.val : ℤ) + n := by
  unfold fwdLift
  have hsub : (q.1 - p.1 : Fin n).val = (n - p.1.val + q.1.val) % n := by
    rw [Fin.sub_def]
  have hp := p.1.isLt
  have hq := q.1.isLt
  by_cases h : p.1.val ≤ q.1.val
  · left
    have h1 : n - p.1.val + q.1.val = (q.1.val - p.1.val) + n := by omega
    have h2 : (n - p.1.val + q.1.val) % n = q.1.val - p.1.val := by
      rw [h1, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsub, h2]
    omega
  · right
    have h2 : (n - p.1.val + q.1.val) % n = n - p.1.val + q.1.val :=
      Nat.mod_eq_of_lt (by omega)
    rw [hsub, h2]
    omega

theorem fwdLift_self {X : Type*} {t : X} {n : ℕ} [NeZero n] (p : CyclePoint X t n) :
    fwdLift p p = (p.1.val : ℤ) := by
  unfold fwdLift
  rw [sub_self]
  simp

/-- The cycle distance: the better of the two relevant lifts. -/
noncomputable def cycleDist (s t : X) {n : ℕ} (p q : CyclePoint X t n) : ℝ :=
  min (chainDist s t p.1.val p.2.val (fwdLift p q) q.2.val)
      (chainDist s t p.1.val p.2.val (fwdLift p q - n) q.2.val)

/-- Monotonicity in the winding number: any lift's chain distance dominates the
cycle distance. -/
theorem cycleDist_le_lift (s t : X) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (p q : CyclePoint X t n) (c : ℤ) :
    cycleDist s t p q ≤ chainDist s t p.1.val p.2.val (fwdLift p q + c * n) q.2.val := by
  have hD : (0 : ℝ) ≤ dist s t := dist_nonneg
  have hn0 : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast hn
  set i : ℤ := (p.1.val : ℤ) with hi
  set F : ℤ := fwdLift p q with hF
  have hFge : i ≤ F := fwdLift_ge p q
  have hFlt : F < i + n := fwdLift_lt p q
  rcases le_or_gt c 0 with hc | hc
  · rcases eq_or_lt_of_le hc with hc0 | hcneg
    · subst hc0
      simp only [zero_mul, add_zero]
      exact min_le_left _ _
    · rcases eq_or_lt_of_le (show c ≤ -1 by omega) with hc1 | hc2
      · subst hc1
        have he : F + (-1) * n = F - n := by ring
        rw [he]
        exact min_le_right _ _
      · -- c ≤ -2 : backward form, dominated by the backward lift
        have hcn : c * (n : ℤ) ≤ -2 * n :=
          mul_le_mul_of_nonneg_right (by omega : c ≤ -2) (le_of_lt hn0)
        have hlt : F + c * n < i := by linarith
        have hlt' : F - n < i := by omega
        refine le_trans (min_le_right _ _) ?_
        unfold chainDist
        rw [if_neg (ne_of_gt hlt'), if_neg (not_lt.mpr hlt'.le),
          if_neg (ne_of_gt hlt), if_neg (not_lt.mpr hlt.le)]
        have hmul : ((i - (F - n) - 1 : ℤ) : ℝ) ≤ ((i - (F + c * n) - 1 : ℤ) : ℝ) := by
          have : (i - (F - n) - 1 : ℤ) ≤ i - (F + c * n) - 1 := by linarith
          exact_mod_cast this
        have := mul_le_mul_of_nonneg_right hmul hD
        linarith
  · -- c ≥ 1 : forward form
    have hcn : (n : ℤ) ≤ c * n := le_mul_of_one_le_left (le_of_lt hn0) (by omega)
    have hgt : i < F + c * n := by linarith
    by_cases hFi : F = i
    · -- same copy: direct distance versus a full loop forward
      refine le_trans (min_le_left _ _) ?_
      unfold chainDist
      rw [if_pos (by omega : i = F), if_neg (ne_of_lt hgt), if_pos hgt]
      have h1 : dist (p.2 : X) (q.2 : X)
          ≤ dist (p.2 : X) t + dist s t + dist s (q.2 : X) := by
        have ha := dist_triangle (p.2 : X) t (q.2 : X)
        have hb := dist_triangle t s (q.2 : X)
        have hc' : dist t s = dist s t := dist_comm t s
        linarith
      have hmul : (1 : ℝ) ≤ ((F + c * n - i - 1 : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ F + c * n - i - 1 := by omega
        exact_mod_cast this
      have h2 := mul_le_mul_of_nonneg_right hmul hD
      rw [one_mul] at h2
      linarith
    · -- distinct copies: bigger forward winding
      have hFgt : i < F := lt_of_le_of_ne hFge (fun hc' => hFi hc'.symm)
      refine le_trans (min_le_left _ _) ?_
      unfold chainDist
      rw [if_neg (ne_of_lt hFgt), if_pos hFgt, if_neg (ne_of_lt hgt), if_pos hgt]
      have hmul : ((F - i - 1 : ℤ) : ℝ) ≤ ((F + c * n - i - 1 : ℤ) : ℝ) := by
        have : (F - i - 1 : ℤ) ≤ F + c * n - i - 1 := by linarith
        exact_mod_cast this
      have := mul_le_mul_of_nonneg_right hmul hD
      linarith

/-- Transfer of a lift across `cycleDist`'s symmetry. -/
theorem cycleDist_symm_le (s t : X) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (p q : CyclePoint X t n) (L : ℤ)
    (hL : L = fwdLift p q ∨ L = fwdLift p q - n) :
    cycleDist s t q p ≤ chainDist s t p.1.val p.2.val L q.2.val := by
  have hshift := chainDist_shift s t L q.2.val (p.1.val : ℤ) p.2.val ((q.1.val : ℤ) - L)
  have hidx1 : L + ((q.1.val : ℤ) - L) = (q.1.val : ℤ) := by ring
  rw [hidx1] at hshift
  have hcm := chainDist_comm s t (p.1.val : ℤ) p.2.val L q.2.val
  rw [hcm, ← hshift]
  have hex : ∃ c : ℤ, (p.1.val : ℤ) + ((q.1.val : ℤ) - L) = fwdLift q p + c * n := by
    rcases hL with hL | hL <;> rcases fwdLift_split p q with hF | hF <;>
      rcases fwdLift_split q p with hG | hG
    · exact ⟨0, by rw [hL, hF, hG]; ring⟩
    · exact ⟨-1, by rw [hL, hF, hG]; ring⟩
    · exact ⟨-1, by rw [hL, hF, hG]; ring⟩
    · exact ⟨-2, by rw [hL, hF, hG]; ring⟩
    · exact ⟨1, by rw [hL, hF, hG]; ring⟩
    · exact ⟨0, by rw [hL, hF, hG]; ring⟩
    · exact ⟨0, by rw [hL, hF, hG]; ring⟩
    · exact ⟨-1, by rw [hL, hF, hG]; ring⟩
  obtain ⟨c, hc⟩ := hex
  rw [hc]
  exact cycleDist_le_lift s t hn q p c

theorem cycleDist_self (s t : X) {n : ℕ} [NeZero n] (p : CyclePoint X t n) :
    cycleDist s t p p = 0 := by
  unfold cycleDist
  rw [fwdLift_self]
  have h1 : chainDist s t (p.1.val : ℤ) p.2.val (p.1.val : ℤ) p.2.val = 0 := by
    unfold chainDist
    rw [if_pos rfl, dist_self]
  rw [h1]
  exact min_eq_left (chainDist_nonneg s t _ _ _ _)

theorem cycleDist_comm (s t : X) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (p q : CyclePoint X t n) :
    cycleDist s t p q = cycleDist s t q p := by
  have key : ∀ p q : CyclePoint X t n, cycleDist s t q p ≤ cycleDist s t p q := by
    intro p q
    have hmin : cycleDist s t p q
        = min (chainDist s t p.1.val p.2.val (fwdLift p q) q.2.val)
            (chainDist s t p.1.val p.2.val (fwdLift p q - n) q.2.val) := rfl
    rw [hmin]
    exact le_min (cycleDist_symm_le s t hn p q _ (Or.inl rfl))
      (cycleDist_symm_le s t hn p q _ (Or.inr rfl))
  exact le_antisymm (key q p) (key p q)

theorem cycleDist_triangle (s t : X) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (p q r : CyclePoint X t n) :
    cycleDist s t p r ≤ cycleDist s t p q + cycleDist s t q r := by
  have main : ∀ L₁ L₂ : ℤ,
      (L₁ = fwdLift p q ∨ L₁ = fwdLift p q - n) →
      (L₂ = fwdLift q r ∨ L₂ = fwdLift q r - n) →
      cycleDist s t p r ≤ chainDist s t p.1.val p.2.val L₁ q.2.val
        + chainDist s t q.1.val q.2.val L₂ r.2.val := by
    intro L₁ L₂ hL₁ hL₂
    have e1 : ∃ a : ℤ, L₁ = (q.1.val : ℤ) + a * n := by
      rcases hL₁ with h | h <;> rcases fwdLift_split p q with hF | hF
      · exact ⟨0, by rw [h, hF]; ring⟩
      · exact ⟨1, by rw [h, hF]; ring⟩
      · exact ⟨-1, by rw [h, hF]; ring⟩
      · exact ⟨0, by rw [h, hF]; ring⟩
    have e2 : ∃ b : ℤ, L₂ = (r.1.val : ℤ) + b * n := by
      rcases hL₂ with h | h <;> rcases fwdLift_split q r with hF | hF
      · exact ⟨0, by rw [h, hF]; ring⟩
      · exact ⟨1, by rw [h, hF]; ring⟩
      · exact ⟨-1, by rw [h, hF]; ring⟩
      · exact ⟨0, by rw [h, hF]; ring⟩
    have e3 : ∃ g : ℤ, fwdLift p r = (r.1.val : ℤ) + g * n := by
      rcases fwdLift_split p r with hF | hF
      · exact ⟨0, by rw [hF]; ring⟩
      · exact ⟨1, by rw [hF]; ring⟩
    obtain ⟨a, ha⟩ := e1
    obtain ⟨b, hb⟩ := e2
    obtain ⟨g, hg⟩ := e3
    have hshift : chainDist s t (q.1.val : ℤ) q.2.val L₂ r.2.val
        = chainDist s t L₁ q.2.val (L₂ + a * n) r.2.val := by
      have h := chainDist_shift s t (q.1.val : ℤ) q.2.val L₂ r.2.val (a * n)
      rw [← ha] at h
      exact h.symm
    have htri := chainDist_triangle s t (p.1.val : ℤ) p.2.val L₁ q.2.val (L₂ + a * n) r.2.val
    have hlift : cycleDist s t p r
        ≤ chainDist s t p.1.val p.2.val (L₂ + a * n) r.2.val := by
      have hc : L₂ + a * n = fwdLift p r + (a + b - g) * n := by rw [hb, hg]; ring
      rw [hc]
      exact cycleDist_le_lift s t hn p r (a + b - g)
    rw [hshift]
    linarith
  have hpq : cycleDist s t p q
      = min (chainDist s t p.1.val p.2.val (fwdLift p q) q.2.val)
          (chainDist s t p.1.val p.2.val (fwdLift p q - n) q.2.val) := rfl
  have hqr : cycleDist s t q r
      = min (chainDist s t q.1.val q.2.val (fwdLift q r) r.2.val)
          (chainDist s t q.1.val q.2.val (fwdLift q r - n) r.2.val) := rfl
  rw [hpq, hqr]
  rcases min_cases (chainDist s t p.1.val p.2.val (fwdLift p q) q.2.val)
      (chainDist s t p.1.val p.2.val (fwdLift p q - n) q.2.val) with ⟨he₁, -⟩ | ⟨he₁, -⟩ <;>
    rcases min_cases (chainDist s t q.1.val q.2.val (fwdLift q r) r.2.val)
        (chainDist s t q.1.val q.2.val (fwdLift q r - n) r.2.val) with ⟨he₂, -⟩ | ⟨he₂, -⟩ <;>
    rw [he₁, he₂]
  · exact main _ _ (Or.inl rfl) (Or.inl rfl)
  · exact main _ _ (Or.inl rfl) (Or.inr rfl)
  · exact main _ _ (Or.inr rfl) (Or.inl rfl)
  · exact main _ _ (Or.inr rfl) (Or.inr rfl)

theorem cycleDist_eq_zero (s t : X) {n : ℕ} [NeZero n] (p q : CyclePoint X t n)
    (h : cycleDist s t p q = 0) : p = q := by
  have hFge := fwdLift_ge p q
  have hFlt := fwdLift_lt p q
  have hone : chainDist s t p.1.val p.2.val (fwdLift p q) q.2.val = 0 ∨
      chainDist s t p.1.val p.2.val (fwdLift p q - n) q.2.val = 0 := by
    rcases min_cases (chainDist s t p.1.val p.2.val (fwdLift p q) q.2.val)
        (chainDist s t p.1.val p.2.val (fwdLift p q - n) q.2.val) with ⟨he, -⟩ | ⟨he, -⟩
    · left
      have hd : cycleDist s t p q
          = chainDist s t p.1.val p.2.val (fwdLift p q) q.2.val := he
      rw [← hd, h]
    · right
      have hd : cycleDist s t p q
          = chainDist s t p.1.val p.2.val (fwdLift p q - n) q.2.val := he
      rw [← hd, h]
  have hD : (0 : ℝ) ≤ dist s t := dist_nonneg
  rcases hone with h0 | h0
  · -- the forward lift vanishes
    unfold chainDist at h0
    by_cases he : (p.1.val : ℤ) = fwdLift p q
    · rw [if_pos he] at h0
      have hxy : (p.2 : X) = (q.2 : X) := by
        rwa [dist_eq_zero] at h0
      have hcopy : p.1 = q.1 := by
        have hsplit := fwdLift_split p q
        have hp := p.1.isLt
        have hq := q.1.isLt
        rcases hsplit with hs | hs
        · exact Fin.ext (by omega)
        · exact absurd hs (by omega)
      exact Prod.ext hcopy (Subtype.ext hxy)
    · rw [if_neg he, if_pos (lt_of_le_of_ne hFge he)] at h0
      exfalso
      have hm : (0 : ℝ) ≤ ((fwdLift p q - p.1.val - 1 : ℤ) : ℝ) * dist s t := by
        have h1 : (0 : ℤ) ≤ fwdLift p q - p.1.val - 1 := by
          have := lt_of_le_of_ne hFge he
          omega
        have h2 : (0 : ℝ) ≤ ((fwdLift p q - p.1.val - 1 : ℤ) : ℝ) := by exact_mod_cast h1
        exact mul_nonneg h2 hD
      have hxt : dist (p.2 : X) t = 0 := by
        have ha := dist_nonneg (x := (p.2 : X)) (y := t)
        have hb := dist_nonneg (x := s) (y := (q.2 : X))
        linarith
      exact p.2.2 (dist_eq_zero.mp hxt)
  · -- the backward lift vanishes: forces `y = t`
    unfold chainDist at h0
    have hlt : fwdLift p q - n < (p.1.val : ℤ) := by omega
    rw [if_neg (ne_of_gt hlt), if_neg (not_lt.mpr hlt.le)] at h0
    exfalso
    have hm : (0 : ℝ) ≤ ((p.1.val - (fwdLift p q - n) - 1 : ℤ) : ℝ) * dist s t := by
      have h1 : (0 : ℤ) ≤ (p.1.val : ℤ) - (fwdLift p q - n) - 1 := by omega
      have h2 : (0 : ℝ) ≤ (((p.1.val : ℤ) - (fwdLift p q - n) - 1 : ℤ) : ℝ) := by
        exact_mod_cast h1
      exact mul_nonneg h2 hD
    have hty : dist t (q.2 : X) = 0 := by
      have ha := dist_nonneg (x := (p.2 : X)) (y := s)
      have hb := dist_nonneg (x := t) (y := (q.2 : X))
      linarith
    exact q.2.2 (dist_eq_zero.mp hty).symm

/-- The **cycle of `n` copies of `X`**, glued `t`-to-`s` around, as a metric space. -/
@[reducible] noncomputable def cycleMetric (X : Type*) [MetricSpace X] (s t : X)
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) : MetricSpace (CyclePoint X t n) where
  dist := cycleDist s t
  dist_self := cycleDist_self s t
  dist_comm := cycleDist_comm s t hn
  dist_triangle p q r := cycleDist_triangle s t hn p q r
  eq_of_dist_eq_zero := cycleDist_eq_zero s t _ _

/-- A point of the `i`-th copy of the cycle. -/
def cyclePt {X : Type*} {t : X} {n : ℕ} (i : Fin n) (x : X) (hx : x ≠ t) :
    CyclePoint X t n := (i, ⟨x, hx⟩)

theorem fwdLift_same {X : Type*} {t : X} {n : ℕ} [NeZero n]
    (p q : CyclePoint X t n) (h : p.1 = q.1) : fwdLift p q = (p.1.val : ℤ) := by
  unfold fwdLift
  rw [← h, sub_self]
  simp

/-- Within one copy, the cycle distance is the original distance. -/
theorem cycleDist_same (s t : X) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (i : Fin n) (x y : X) (hx : x ≠ t) (hy : y ≠ t) :
    cycleDist s t (cyclePt i x hx) (cyclePt i y hy) = dist x y := by
  unfold cycleDist
  rw [fwdLift_same (cyclePt i x hx) (cyclePt i y hy) rfl]
  have h1 : chainDist s t ((cyclePt i x hx).1.val : ℤ) ((cyclePt i x hx).2 : X)
      ((cyclePt i x hx).1.val : ℤ) ((cyclePt (t := t) i y hy).2 : X) = dist x y := by
    unfold chainDist
    rw [if_pos rfl]
    rfl
  rw [h1]
  refine min_eq_left ?_
  have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have h2 : chainDist s t ((cyclePt i x hx).1.val : ℤ) ((cyclePt i x hx).2 : X)
      (((cyclePt i x hx).1.val : ℤ) - n) ((cyclePt (t := t) i y hy).2 : X)
      = dist x s + (((i.val : ℤ) - ((i.val : ℤ) - n) - 1 : ℤ) : ℝ) * dist s t + dist t y := by
    unfold chainDist
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  rw [h2]
  have hco : (((i.val : ℤ) - ((i.val : ℤ) - n) - 1 : ℤ) : ℝ) = ((n : ℝ)) - 1 := by
    push_cast
    ring
  rw [hco]
  have h3 : dist x y ≤ dist x s + dist s t + dist t y := by
    have ha := dist_triangle x s y
    have hb := dist_triangle s t y
    linarith
  have h4 : dist s t ≤ ((n : ℝ) - 1) * dist s t := by
    have : (1 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    nlinarith [dist_nonneg (x := s) (y := t)]
  linarith

/-- Across distinct copies, the cycle distance is the better of the two ways around. -/
theorem cycleDist_cross (s t : X) {n : ℕ} [NeZero n]
    (i j : Fin n) (hij : i ≠ j) (x y : X) (hx : x ≠ t) (hy : y ≠ t) :
    cycleDist s t (cyclePt i x hx) (cyclePt j y hy)
      = min (dist x t + (((j - i : Fin n).val : ℝ) - 1) * dist s t + dist s y)
          (dist x s + ((n : ℝ) - ((j - i : Fin n).val : ℝ) - 1) * dist s t + dist t y) := by
  have hoff1 : 1 ≤ ((j - i : Fin n)).val := by
    rcases Nat.eq_zero_or_pos ((j - i : Fin n)).val with h0 | h1
    · exfalso
      have : (j - i : Fin n) = 0 := Fin.ext h0
      have := sub_eq_zero.mp this
      exact hij this.symm
    · exact h1
  have hoffn : ((j - i : Fin n)).val < n := (j - i : Fin n).isLt
  unfold cycleDist fwdLift
  have hfe : ((cyclePt (t := t) j y hy).1 - (cyclePt (t := t) i x hx).1 : Fin n)
      = (j - i : Fin n) := rfl
  congr 1
  · -- forward route
    unfold chainDist
    rw [if_neg (by
      show ¬ ((i.val : ℤ) = (i.val : ℤ) + ((j - i : Fin n).val : ℤ))
      omega), if_pos (by
      show (i.val : ℤ) < (i.val : ℤ) + ((j - i : Fin n).val : ℤ)
      omega)]
    show dist x t + (((i.val : ℤ) + ((j - i : Fin n).val : ℤ) - (i.val : ℤ) - 1 : ℤ) : ℝ)
          * dist s t + dist s y
        = dist x t + (((j - i : Fin n).val : ℝ) - 1) * dist s t + dist s y
    push_cast
    ring
  · -- backward route
    unfold chainDist
    rw [if_neg (by
      show ¬ ((i.val : ℤ) = (i.val : ℤ) + ((j - i : Fin n).val : ℤ) - n)
      omega), if_neg (by
      show ¬ ((i.val : ℤ) < (i.val : ℤ) + ((j - i : Fin n).val : ℤ) - n)
      omega)]
    show dist x s + (((i.val : ℤ) - ((i.val : ℤ) + ((j - i : Fin n).val : ℤ) - n) - 1 : ℤ) : ℝ)
          * dist s t + dist t y
        = dist x s + ((n : ℝ) - ((j - i : Fin n).val : ℝ) - 1) * dist s t + dist t y
    push_cast
    ring

instance {X : Type*} [DecidableEq X] {t : X} {n : ℕ} :
    DecidableEq (CyclePoint X t n) :=
  inferInstanceAs (DecidableEq (Fin n × {x : X // x ≠ t}))

noncomputable instance {X : Type*} [Fintype X] {t : X} {n : ℕ} :
    Fintype (CyclePoint X t n) := by
  classical
  exact inferInstanceAs (Fintype (Fin n × {x : X // x ≠ t}))

theorem card_cyclePoint (X : Type*) [Fintype X] [DecidableEq X] (t : X) (n : ℕ) :
    Fintype.card (CyclePoint X t n) = n * (Fintype.card X - 1) := by
  classical
  have h1 : Fintype.card (CyclePoint X t n)
      = Fintype.card (Fin n) * Fintype.card {x : X // x ≠ t} := by
    convert Fintype.card_prod (Fin n) {x : X // x ≠ t} using 2
  have h2 : Fintype.card {x : X // x ≠ t} = Fintype.card X - 1 := by
    have := Fintype.card_subtype_compl (fun x : X => x = t)
    simpa [Fintype.card_subtype_eq] using this
  rw [h1, h2, Fintype.card_fin]

end KServer


