-- Prove2me | solution 1 for BerggrenHypercycleStars.exists_seed_slope_close
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:35:23.383456+00:00
-- url     : https://prove2.me/submissions/bcddd3e0-19a1-4f31-b2a8-5e1b70d858ee

-- Sol generated from Cryptography/BerggrenStars/BoundaryLimitSet.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars

/-!
# Where the stars come from: the boundary limit set of the Berggren tree

The hypercycle stars of `Cryptography.BerggrenStars.HypercycleStars` sit over rational boundary
points. This file shows that the tree accumulates on *every* point of the boundary interval
`[0,1]`, so the visible rays are not an artifact of a few special cusps: the picture is a set of
curves radiating out of a dense set of boundary points.

The construction is completely explicit and uses only dyadic seeds: for `m = 2^j` every odd
`n < m` gives a Euclid seed (coprimality is automatic, opposite parity is automatic), and the
slopes `n / 2^j` with `n` odd are dense in `(0,1)`.

## Main results

* `isSeed_two_pow` : the dyadic seeds.
* `exists_seed_slope_close` : every `t ∈ (0,1)` is approximated to within `ε` by the slope `n/m`
  of a Euclid seed, with `1/m < ε` as well (the node is also close to the boundary).
* `exists_node_close_to_boundary` : every `t ∈ (0,1)` is a limit of Berggren nodes in `ℂ`; the
  limit set of the embedded tree contains the whole boundary interval.
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane

/-- Dyadic seeds: for `j ≥ 1` and odd `n < 2^j`, the pair `(2^j, n)` is a Euclid seed. -/
theorem isSeed_two_pow (j n : ℕ) (hj : 1 ≤ j) (hn : 0 < n) (hlt : n < 2 ^ j)
    (hodd : n % 2 = 1) : IsSeed (2 ^ j) n := by
  refine ⟨hn, hlt, ?_, ?_⟩
  · have h2 : Nat.Coprime 2 n := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    exact Nat.Coprime.pow_left j h2
  · have heven : 2 ^ j % 2 = 0 := by
      have : (2 : ℕ) ∣ 2 ^ j := dvd_pow_self 2 (by omega)
      omega
    omega




open BerggrenHypercycleStars in
theorem solution(t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ m n : ℕ, IsSeed m n ∧ |(n : ℝ) / m - t| < ε ∧ 1 / (m : ℝ) < ε := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, max (2 / ε) (2 / (1 - t)) < (2 : ℝ) ^ j :=
    pow_unbounded_of_one_lt _ (by norm_num)
  set M : ℕ := 2 ^ j with hM
  have hMR : ((M : ℕ) : ℝ) = (2 : ℝ) ^ j := by rw [hM]; push_cast; ring
  have hMpos : (0 : ℝ) < (M : ℝ) := by rw [hMR]; positivity
  have hεM : 2 / ε < (M : ℝ) := by rw [hMR]; exact lt_of_le_of_lt (le_max_left _ _) hj
  have htM : 2 / (1 - t) < (M : ℝ) := by rw [hMR]; exact lt_of_le_of_lt (le_max_right _ _) hj
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hM2 : (2 : ℝ) < (M : ℝ) := by
    have h2le : (2 : ℝ) ≤ 2 / (1 - t) := by
      rw [le_div_iff₀ h1t]; nlinarith
    linarith
  have hj1 : 1 ≤ j := by
    by_contra hcon
    have hj0 : j = 0 := by omega
    rw [hj0] at hMR
    norm_num at hMR
    rw [hMR] at hM2
    norm_num at hM2
  -- the odd integer nearest to `t * M`
  set k : ℕ := ⌊t * (M : ℝ) / 2⌋₊ with hk
  have hkle : (k : ℝ) ≤ t * (M : ℝ) / 2 := Nat.floor_le (by positivity)
  have hklt : t * (M : ℝ) / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  set n : ℕ := 2 * k + 1 with hn
  have hnR : (n : ℝ) = 2 * (k : ℝ) + 1 := by rw [hn]; push_cast; ring
  have habs : |(n : ℝ) - t * M| ≤ 1 := by
    rw [hnR, abs_le]
    constructor <;> linarith
  have hnlt : n < M := by
    have hup : (n : ℝ) ≤ t * M + 1 := by linarith [(abs_le.1 habs).2]
    have hMt : 2 < (M : ℝ) * (1 - t) := by
      rw [div_lt_iff₀ h1t] at htM; linarith
    have : (n : ℝ) < (M : ℝ) := by nlinarith
    exact_mod_cast this
  have hMlarge : 1 / (M : ℝ) < ε := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hεM
    nlinarith
  refine ⟨M, n, isSeed_two_pow j n hj1 (by omega) (by rw [← hM]; exact hnlt) (by omega), ?_,
    hMlarge⟩
  have hdiv : (n : ℝ) / M - t = ((n : ℝ) - t * M) / (M : ℝ) := by field_simp
  rw [hdiv, abs_div, abs_of_pos hMpos]
  have h1 : |(n : ℝ) - t * M| / (M : ℝ) ≤ 1 / (M : ℝ) :=
    (div_le_div_iff_of_pos_right hMpos).mpr habs
  linarith
