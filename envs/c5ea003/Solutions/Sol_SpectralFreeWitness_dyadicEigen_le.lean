-- Prove2me | solution 1 for SpectralFreeWitness.dyadicEigen_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:43:15.977346+00:00
-- url     : https://prove2.me/submissions/6fbe82ae-f958-4854-9143-8dfe0edd7535

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Theorems.Thm_SpectralFreeWitness_cdist_pow_two
import Theorems.Thm_SpectralFreeWitness_cos_nonpos_of_cdist
/-
# The Spectral Free-Witness: Heat-Kernel Order Recovery

This file gives a complete, self-contained formal proof of the mechanism behind the
"heat-kernel free witness": the multiplicative order `r = ord_N(b)` is recovered
*exactly* from a **single** heat-kernel (return-probability) value of a half-lazy
random walk on the cyclic group `Z/rZ` with **lacunary dyadic** generators
`{±2^t : 0 ≤ t ≤ M}`, after `n = 8 (M+1)^2` diffusion steps, where `2^M ≥ N`.

The chain of results proved here:

* `cdist_double` — the *doubling step*: as long as the circle distance
  `d(x) = min (x % r) (r - x % r)` is below `r/4`, doubling `x` doubles `d`.
* `exists_dyadic_quarter` — the **doubling lemma**: for every `x ≢ 0 (mod r)`
  there is a dyadic shift `t ≤ M` (`r ≤ 2^M`) with `2^t x mod r ∈ [r/4, 3r/4]`.
* `cos_nonpos_of_cdist`, `dyadicEigen_le` — the resulting **spectral gap**:
  every nontrivial character eigenvalue satisfies `λ_k ≤ 1 - 1/(M+1)`, hence the
  half-lazy eigenvalue satisfies `0 ≤ μ_k ≤ 1 - 1/(2(M+1))`.
* `heatReturn_lower`, `heatReturn_upper` — the heat kernel at the identity
  satisfies `1/r ≤ p_n(e) ≤ 1/r + (1 - 1/(2(M+1)))^n`.
* `beta_pow_le` — the mixing estimate at the empirically observed step count
  `n = 8(M+1)^2`: the error is at most `1/(4N²)`.
* `round_one_div_of_close` — the rounding step.
* `heat_kernel_order_recovery` — **main theorem**: `round (1 / p_n(e)) = r`.
* `heat_kernel_recovers_orderOf` — the arithmetic corollary for the
  multiplicative order of a unit `b ∈ (Z/NZ)ˣ`.

Everything is unconditional; no `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real

/-! ## 1. Circle distance and the doubling lemma -/


lemma cdist_pos_of_ne (r x : ℕ) (hr : 0 < r) (hx : x % r ≠ 0) : 0 < cdist r x := by
  have h : x % r < r := Nat.mod_lt _ hr
  simp only [cdist, lt_min_iff]
  omega




/-- **The doubling lemma.** If `x ≢ 0 (mod r)` and `r ≤ 2^M`, then some lacunary
dyadic shift `2^t x`, `t ≤ M`, lands in the "far" arc `[r/4, 3r/4]` of the circle. -/
theorem exists_dyadic_quarter (r x M : ℕ) (hr : 0 < r) (hx : x % r ≠ 0) (hM : r ≤ 2 ^ M) :
    ∃ t ≤ M, r ≤ 4 * cdist r (2 ^ t * x) := by
  by_contra hcon
  push_neg at hcon
  have hstay : ∀ t ≤ M, 4 * cdist r (2 ^ t * x) < r := fun t ht => hcon t ht
  have hM' := cdist_pow_two r x M hr hx hstay M le_rfl
  have hpos := cdist_pos_of_ne r x hr hx
  have hlast := hstay M le_rfl
  rw [hM'] at hlast
  have hbig : 4 * 2 ^ M ≤ 4 * (2 ^ M * cdist r x) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hpos)
  omega

/-! ## 2. From the doubling lemma to a negative cosine -/


/-! ## 3. Spectral data of the lacunary dyadic walk -/











/-! ## 4. The heat kernel value at the identity -/



/-! ## 5. Mixing at `n = 8 (M+1)²` steps -/


/-! ## 6. Rounding recovers the order exactly -/


/-! ## 7. Main theorem: heat-kernel order recovery -/




open SpectralFreeWitness in
theorem solution(r M k : ℕ) (hr : 0 < r) (hk : k % r ≠ 0) (hM : r ≤ 2 ^ M) :
    dyadicEigen r M k ≤ 1 - 1 / ((M : ℝ) + 1) := by
  obtain ⟨t₀, ht₀, hfar⟩ := exists_dyadic_quarter r k M hr hk hM
  have hmem : t₀ ∈ range (M + 1) := mem_range.mpr (by omega)
  set f : ℕ → ℝ := fun t => Real.cos (2 * π * ((k * 2 ^ t : ℕ) : ℝ) / r) with hf
  have hft₀ : f t₀ ≤ 0 := by
    have hcomm : (k * 2 ^ t₀ : ℕ) = 2 ^ t₀ * k := by ring
    have := cos_nonpos_of_cdist r (2 ^ t₀ * k) hr hfar
    rw [hf]
    simpa [hcomm] using this
  have hsplit : ∑ t ∈ range (M + 1), f t = f t₀ + ∑ t ∈ (range (M + 1)).erase t₀, f t :=
    (Finset.add_sum_erase _ _ hmem).symm
  have hrest : ∑ t ∈ (range (M + 1)).erase t₀, f t ≤ (M : ℝ) := by
    calc ∑ t ∈ (range (M + 1)).erase t₀, f t ≤ ∑ _t ∈ (range (M + 1)).erase t₀, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => Real.cos_le_one _)
      _ = (((range (M + 1)).erase t₀).card : ℝ) := by simp
      _ = (M : ℝ) := by
          rw [Finset.card_erase_of_mem hmem, card_range, Nat.add_sub_cancel]
  have hsum : ∑ t ∈ range (M + 1), f t ≤ (M : ℝ) := by rw [hsplit]; linarith
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [dyadicEigen, div_le_iff₀ hpos]
  have hrhs : (1 - 1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1) = (M : ℝ) := by
    field_simp
    ring
  rw [hrhs]
  exact hsum
