-- Prove2me | solution 1 for BanditAlgorithm.tsum_weight_of_tail_cover
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T16:07:06.154413+00:00
-- url     : https://prove2.me/submissions/8bd0d603-d591-4ef3-9630-f26299958346

import Definitions.Def_TrackAndStop

/-!
# Trading a moment for a delay

If the failures of one family are covered by the failures of another *from a
delayed round on*, the weighted failure series of the first converges as soon as
the quadratically weighted series of the second does.

The mechanism is an exchange of sums, free in `ℝ≥0∞` with no summability side
condition.  A single failure of `B` at round `m` can spoil only the rounds `n`
with `θn ≤ m`, and their total weight is

  `∑_{n : θn ≤ m} (n+1) ≤ (⌈1/θ⌉+1)²·(m+1)²`,

so the weight `(n+1)` on `A` becomes `(m+1)²` on `B`.  The delay constant is kept
a natural number, which avoids carrying `ℝ≥0∞`-valued real arithmetic through the
exchange.

The covering hypothesis is allowed to fail off a null set `G`, since in the
application it holds only on the trajectories a policy actually produces.
-/

open MeasureTheory ENNReal Filter Topology

namespace BanditAlgorithm

/-! ## The delay constant -/

/-- `⌈1/θ⌉ + 1`, the natural number for which `⌈m/θ⌉ + 1 ≤ delayConst θ · (m+1)`. -/
noncomputable def delayConst (θ : ℝ) : ℕ := ⌈1 / θ⌉₊ + 1

theorem ceil_div_succ_le {θ : ℝ} (hθ : 0 < θ) (m : ℕ) :
    ⌈(m : ℝ) / θ⌉₊ + 1 ≤ delayConst θ * (m + 1) := by
  have hx : (0 : ℝ) ≤ 1 / θ := by positivity
  -- `⌈m·x⌉ ≤ m·⌈x⌉`, since `m·x ≤ m·⌈x⌉` and the right side is an integer
  have hceil : ⌈(m : ℝ) / θ⌉₊ ≤ m * ⌈1 / θ⌉₊ := by
    refine Nat.ceil_le.mpr ?_
    have hle : (m : ℝ) * (1 / θ) ≤ (m : ℝ) * (⌈1 / θ⌉₊ : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg m)
    calc (m : ℝ) / θ = (m : ℝ) * (1 / θ) := by ring
      _ ≤ (m : ℝ) * (⌈1 / θ⌉₊ : ℝ) := hle
      _ = ((m * ⌈1 / θ⌉₊ : ℕ) : ℝ) := by push_cast; ring
  unfold delayConst
  calc ⌈(m : ℝ) / θ⌉₊ + 1 ≤ m * ⌈1 / θ⌉₊ + 1 := by omega
    _ ≤ (⌈1 / θ⌉₊ + 1) * (m + 1) := by nlinarith [Nat.zero_le (⌈1 / θ⌉₊), Nat.zero_le m]

/-! ## Counting the rounds one failure can spoil -/

/-- The rounds `n` whose delayed threshold `⌈θn⌉` has not passed `m` all lie below
`m/θ`, so their total weight is quadratic in `m`. -/
theorem tsum_weight_of_ceil_le {θ : ℝ} (hθ : 0 < θ) (m : ℕ) :
    ∑' n : ℕ, (if ⌈θ * (n : ℝ)⌉₊ ≤ m then ((n : ℝ≥0∞) + 1) else 0)
      ≤ ((delayConst θ : ℝ≥0∞)) ^ 2 * (((m : ℝ≥0∞) + 1) ^ 2) := by
  classical
  set J : ℕ := ⌈(m : ℝ) / θ⌉₊ with hJdef
  -- only rounds below `J` contribute
  have hsupp : ∀ n : ℕ, ⌈θ * (n : ℝ)⌉₊ ≤ m → n ∈ Finset.range (J + 1) := by
    intro n hn
    have h1 : θ * (n : ℝ) ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 : (n : ℝ) ≤ (m : ℝ) / θ := by rw [le_div_iff₀ hθ]; linarith
    have h3 : (n : ℝ) ≤ (J : ℝ) := le_trans h2 (Nat.le_ceil _)
    have h4 : n ≤ J := by exact_mod_cast h3
    exact Finset.mem_range.mpr (by omega)
  -- so the sum is a finite one
  set f : ℕ → ℝ≥0∞ := fun n ↦ if ⌈θ * (n : ℝ)⌉₊ ≤ m then ((n : ℝ≥0∞) + 1) else 0 with hfdef
  have hzero : ∀ n ∉ Finset.range (J + 1), f n = 0 := by
    intro n hn
    rw [hfdef]
    by_cases hc : ⌈θ * (n : ℝ)⌉₊ ≤ m
    · exact absurd (hsupp n hc) hn
    · simp [hc]
  have hsum : ∑' n : ℕ, f n = ∑ n ∈ Finset.range (J + 1), f n := tsum_eq_sum hzero
  rw [hsum]
  -- each term is at most `J + 1`, and there are `J + 1` of them
  have hterm : ∀ n ∈ Finset.range (J + 1), f n ≤ ((J : ℝ≥0∞) + 1) := by
    intro n hn
    rw [hfdef]
    by_cases hc : ⌈θ * (n : ℝ)⌉₊ ≤ m
    · simp only [if_pos hc]
      have : (n : ℝ≥0∞) ≤ (J : ℝ≥0∞) := by
        exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      gcongr
    · simp [hc]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  -- `(J+1)² ≤ (delayConst θ)²·(m+1)²`
  have hnat : (J + 1 : ℕ) ≤ delayConst θ * (m + 1) := ceil_div_succ_le hθ m
  have hcast : ((J : ℝ≥0∞) + 1) ≤ (delayConst θ : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) := by
    have h : ((J + 1 : ℕ) : ℝ≥0∞) ≤ ((delayConst θ * (m + 1) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hnat
    push_cast at h
    exact h
  calc ((J : ℝ≥0∞) + 1) * ((J : ℝ≥0∞) + 1)
      ≤ ((delayConst θ : ℝ≥0∞) * ((m : ℝ≥0∞) + 1))
          * ((delayConst θ : ℝ≥0∞) * ((m : ℝ≥0∞) + 1)) := mul_le_mul' hcast hcast
    _ = (delayConst θ : ℝ≥0∞) ^ 2 * (((m : ℝ≥0∞) + 1) ^ 2) := by ring


end BanditAlgorithm

open BanditAlgorithm

/-! ## The exchange -/

/-- **Trading a moment for a delay.**  If the failures of `A` at round `n` are
covered by the failures of `B` from round `⌈θn⌉` on, then the weighted series for
`A` converges as soon as the *quadratically* weighted series for `B` does. -/
theorem solution {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {A B : ℕ → Set α} {G : Set α} (hG : ν Gᶜ = 0)
    {θ : ℝ} (hθ : 0 < θ) {N₀ : ℕ}
    (hcover : ∀ n : ℕ, N₀ ≤ n →
      (A n)ᶜ ∩ G ⊆ ⋃ m : {m : ℕ // ⌈θ * (n : ℝ)⌉₊ ≤ m}, (B (m : ℕ))ᶜ)
    (hB : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) ^ 2 * ν (B m)ᶜ ≠ ⊤) :
    ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * ν (A n)ᶜ ≠ ⊤ := by
  classical
  -- split into the head, which is a finite sum, and the tail
  set head : ℕ → ℝ≥0∞ := fun n ↦ if n < N₀ then ((n : ℝ≥0∞) + 1) else 0 with hheaddef
  set tail : ℕ → ℝ≥0∞ := fun n ↦
    if N₀ ≤ n then ((n : ℝ≥0∞) + 1) * ν (A n)ᶜ else 0 with htaildef
  have hsplit : ∀ n : ℕ, ((n : ℝ≥0∞) + 1) * ν (A n)ᶜ ≤ head n + tail n := by
    intro n
    by_cases hn : N₀ ≤ n
    · have : ¬ n < N₀ := by omega
      simp only [hheaddef, htaildef, if_neg this, if_pos hn, zero_add]
      exact le_rfl
    · have hlt : n < N₀ := by omega
      simp only [hheaddef, htaildef, if_pos hlt, if_neg hn, add_zero]
      exact mul_le_of_le_one_right' prob_le_one
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsplit)
  rw [ENNReal.tsum_add]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · -- the head is a finite sum of finite terms
    have hzero : ∀ n ∉ Finset.range N₀, head n = 0 := by
      intro n hn
      have : ¬ n < N₀ := fun hc ↦ hn (Finset.mem_range.mpr hc)
      simp [hheaddef, this]
    rw [tsum_eq_sum hzero]
    refine (ENNReal.sum_lt_top.mpr fun n _ ↦ ?_).ne
    rw [hheaddef]
    by_cases hc : n < N₀
    · simp only [if_pos hc]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top n, one_lt_top⟩
    · simp [hc]
  · -- the tail, by covering and exchanging
    have hbound : ∀ n, tail n
        ≤ ((n : ℝ≥0∞) + 1) *
            ∑' m : ℕ, (if ⌈θ * (n : ℝ)⌉₊ ≤ m then ν (B m)ᶜ else 0) := by
      intro n
      rw [htaildef]
      by_cases hn : N₀ ≤ n
      · simp only [if_pos hn]
        refine mul_le_mul_left' ?_ _
        have hinter : ν (A n)ᶜ = ν ((A n)ᶜ ∩ G) := by
          refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
          have hcov : (A n)ᶜ ⊆ ((A n)ᶜ ∩ G) ∪ Gᶜ := by
            intro x hx
            by_cases hg : x ∈ G
            · exact Or.inl ⟨hx, hg⟩
            · exact Or.inr hg
          refine le_trans (measure_mono hcov) ?_
          refine le_trans (measure_union_le _ _) ?_
          rw [hG, add_zero]
        rw [hinter]
        refine le_trans (measure_mono (hcover n hn)) ?_
        refine le_trans (measure_iUnion_le _) ?_
        have hinj : Function.Injective
            (Subtype.val : {m : ℕ // ⌈θ * (n : ℝ)⌉₊ ≤ m} → ℕ) := Subtype.val_injective
        have heq : ∀ x : {m : ℕ // ⌈θ * (n : ℝ)⌉₊ ≤ m},
            ν (B (x : ℕ))ᶜ
              = (if ⌈θ * (n : ℝ)⌉₊ ≤ (x : ℕ) then ν (B (x : ℕ))ᶜ else 0) := by
          intro x; rw [if_pos x.2]
        rw [tsum_congr heq]
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj _
      · simp [hn]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    -- pull the weight inside and exchange
    have hexp : ∀ n : ℕ, ((n : ℝ≥0∞) + 1) *
          ∑' m : ℕ, (if ⌈θ * (n : ℝ)⌉₊ ≤ m then ν (B m)ᶜ else 0)
        = ∑' m : ℕ, (if ⌈θ * (n : ℝ)⌉₊ ≤ m then ((n : ℝ≥0∞) + 1) else 0) * ν (B m)ᶜ := by
      intro n
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun m ↦ ?_
      by_cases hm : ⌈θ * (n : ℝ)⌉₊ ≤ m <;> simp [hm]
    rw [tsum_congr hexp, ENNReal.tsum_comm]
    have hinner : ∀ m : ℕ,
        ∑' n : ℕ, (if ⌈θ * (n : ℝ)⌉₊ ≤ m then ((n : ℝ≥0∞) + 1) else 0) * ν (B m)ᶜ
          ≤ (delayConst θ : ℝ≥0∞) ^ 2 * (((m : ℝ≥0∞) + 1) ^ 2 * ν (B m)ᶜ) := by
      intro m
      rw [ENNReal.tsum_mul_right]
      calc (∑' n : ℕ, (if ⌈θ * (n : ℝ)⌉₊ ≤ m then ((n : ℝ≥0∞) + 1) else 0)) * ν (B m)ᶜ
          ≤ ((delayConst θ : ℝ≥0∞) ^ 2 * (((m : ℝ≥0∞) + 1) ^ 2)) * ν (B m)ᶜ :=
            mul_le_mul_right' (tsum_weight_of_ceil_le hθ m) _
        _ = (delayConst θ : ℝ≥0∞) ^ 2 * (((m : ℝ≥0∞) + 1) ^ 2 * ν (B m)ᶜ) := by ring
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hinner)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (by simp [ENNReal.natCast_ne_top]) hB

