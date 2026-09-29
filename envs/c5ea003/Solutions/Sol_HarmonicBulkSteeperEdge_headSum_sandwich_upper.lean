-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headSum_sandwich_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:42:56.86309+00:00
-- url     : https://prove2.me/submissions/8b372956-e513-4644-bc48-8c14bcf476ca

-- Sol generated from Probability/SubHarmonicSaturationRate.lean
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
/-
  # The saturation rate below the harmonic exponent

  `Probability.HarmonicBulkSteeperEdge` proves the *saturation dichotomy* for the head
  statistic of a discrete power-law kernel `k ↦ k ^ (-a)` on `{1, …, n}`: the head mass of
  a fixed window `{1, …, m}` tends to a positive limit iff `a > 1`, and collapses to `0`
  for `a ≤ 1`.  `Probability.HarmonicSaturationRate` pins the *rate* of that collapse at
  the harmonic exponent `a = 1`, where it is logarithmic: `headMass 1 n m · log n → H(m)`.

  This file closes the remaining half of the rate question — the *sub-harmonic* regime
  `0 ≤ a < 1`, where the collapse is polynomial rather than logarithmic:

  * `headSum_sandwich_lower` / `headSum_sandwich_upper` — the non-asymptotic two-sided
    bound `((n+1)^{1-a} - 1)/(1-a) ≤ headSum a n ≤ 1 + (n^{1-a} - 1)/(1-a)`, obtained by
    monotone sum/integral comparison for the antitone kernel `x ↦ x^{-a}`.
  * `headSum_div_rpow_tendsto` — consequently `headSum a n / n^{1-a} → 1/(1-a)`.
  * `headMass_mul_rpow_tendsto` — the rate itself:
    `headMass a n m · n^{1-a} → (1-a) · headSum a m`.
  * `headMass_doubling_ratio_tendsto` — the calibration corollary: *doubling* the
    truncation multiplies the dial asymptotically by `2^{a-1}`.  (Contrast the harmonic
    case, where doubling is asymptotically neutral and *squaring* halves the dial.)

  Together with `HarmonicSaturationRate` this fixes the truncation artefact for every
  exponent `a ≤ 1`, so recorded dials taken at different truncations become comparable:
  at `a < 1` the level scales like `n^{a-1}`, at `a = 1` like `1 / log n`, and only for
  `a > 1` does it saturate.
-/

open Filter Topology

open HarmonicBulkSteeperEdge

/-! ## The kernel is antitone on the positive reals -/

/-- For a nonnegative exponent the real kernel `x ↦ x ^ (-a)` is antitone on any interval
contained in the positive reals. -/
lemma antitoneOn_rpow_neg {a : ℝ} (ha : 0 ≤ a) {u v : ℝ} (hu : 0 < u) :
    AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Icc u v) := by
  intro x hx _ _ hxy
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hu hx.1) hxy (by linarith)

/-! ## Non-asymptotic sandwich for the truncated sum -/



/-! ## The polynomial rate -/





open HarmonicBulkSteeperEdge in
theorem solution{a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {n : ℕ} (hn : 1 ≤ n) :
    headSum a n ≤ 1 + ((n : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Icc ((1 : ℕ) : ℝ) ((n : ℕ) : ℝ)) := by
    push_cast
    exact antitoneOn_rpow_neg ha one_pos
  have hkey := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (-a)) (a := 1) (b := n)
    hn hanti
  rw [integral_rpow (Or.inl (by linarith))] at hkey
  have hre : ∑ i ∈ Finset.Ico 1 n, ((((i + 1 : ℕ)) : ℝ)) ^ (-a) = headSum a n - 1 := by
    have h1 : ∑ i ∈ Finset.Ico 1 n, ((((i + 1 : ℕ)) : ℝ)) ^ (-a)
        = ∑ i ∈ Finset.Ico 2 (n + 1), ((i : ℝ)) ^ (-a) := by
      rw [← Finset.sum_Ico_add' (fun i : ℕ => ((i : ℝ)) ^ (-a)) 1 n 1]
    rw [h1, Finset.Ico_add_one_right_eq_Icc]
    have h2 : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [headSum, h2, Finset.sum_insert (by simp)]
    simp [pw]
  rw [hre] at hkey
  push_cast at hkey
  have he : (-a + 1) = 1 - a := by ring
  rw [he] at hkey
  simp only [Real.one_rpow] at hkey
  linarith
