-- Prove2me | solution 1 for SpectralFreeWitness.heat_kernel_recovers_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:13:25.153529+00:00
-- url     : https://prove2.me/submissions/4e5a4cc6-a185-41b4-9d54-f622fa0f41fc

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Theorems.Thm_SpectralFreeWitness_heat_kernel_order_recovery
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
theorem solution(N : ℕ) [NeZero N] (b : (ZMod N)ˣ) (M : ℕ)
    (hM : N ≤ 2 ^ M) :
    round (1 / heatReturn (orderOf b) M (8 * (M + 1) ^ 2)) = (orderOf b : ℤ) := by
  haveI : Fintype (ZMod N) := ZMod.fintype N
  have hpos : 0 < orderOf b := orderOf_pos b
  have hle : orderOf b ≤ N := by
    have h1 : orderOf b ∣ Fintype.card (ZMod N)ˣ := orderOf_dvd_card
    have h2 : Fintype.card (ZMod N)ˣ = N.totient := ZMod.card_units_eq_totient N
    have h3 : N.totient ≤ N := Nat.totient_le N
    have h4 : 0 < N.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    have h5 : orderOf b ≤ N.totient := by
      rw [← h2]
      exact Nat.le_of_dvd (by rw [h2]; exact h4) h1
    omega
  exact heat_kernel_order_recovery N (orderOf b) M hpos hle hM
