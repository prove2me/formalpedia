-- Prove2me | solution 1 for SpectralFreeWitness.cos_nonpos_of_cdist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:41:43.966355+00:00
-- url     : https://prove2.me/submissions/efafafcf-dc11-4970-b39e-6a20079ec1ab

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
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







/-! ## 2. From the doubling lemma to a negative cosine -/


/-! ## 3. Spectral data of the lacunary dyadic walk -/











/-! ## 4. The heat kernel value at the identity -/



/-! ## 5. Mixing at `n = 8 (M+1)²` steps -/


/-! ## 6. Rounding recovers the order exactly -/


/-! ## 7. Main theorem: heat-kernel order recovery -/




open SpectralFreeWitness in
theorem solution(r x : ℕ) (hr : 0 < r) (h : r ≤ 4 * cdist r x) :
    Real.cos (2 * π * (x : ℝ) / r) ≤ 0 := by
  have hlt : x % r < r := Nat.mod_lt _ hr
  have h1 : r ≤ 4 * (x % r) := by
    simp only [cdist] at h; omega
  have h2 : 4 * (x % r) ≤ 3 * r := by
    simp only [cdist] at h; omega
  have hx : (x : ℝ) = ((x % r : ℕ) : ℝ) + (r : ℝ) * ((x / r : ℕ) : ℝ) := by
    have hd : r * (x / r) + x % r = x := Nat.div_add_mod x r
    have hc : ((r * (x / r) + x % r : ℕ) : ℝ) = ((x : ℕ) : ℝ) := by rw [hd]
    push_cast at hc
    linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hsplit : 2 * π * (x : ℝ) / r
      = 2 * π * ((x % r : ℕ) : ℝ) / r + ((x / r : ℕ) : ℝ) * (2 * π) := by
    rw [hx]; field_simp
  rw [hsplit, Real.cos_add_nat_mul_two_pi]
  have hpi := Real.pi_pos
  have hc1 : π / 2 ≤ 2 * π * ((x % r : ℕ) : ℝ) / r := by
    rw [le_div_iff₀ hr0]
    have hcast : (r : ℝ) ≤ 4 * ((x % r : ℕ) : ℝ) := by exact_mod_cast h1
    nlinarith
  have hc2 : 2 * π * ((x % r : ℕ) : ℝ) / r ≤ π + π / 2 := by
    rw [div_le_iff₀ hr0]
    have hcast : 4 * ((x % r : ℕ) : ℝ) ≤ 3 * (r : ℝ) := by exact_mod_cast h2
    nlinarith
  exact Real.cos_nonpos_of_pi_div_two_le_of_le hc1 hc2
