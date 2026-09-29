-- Prove2me | solution 1 for A4ForkPinning.info_all_split_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:18:26.336246+00:00
-- url     : https://prove2.me/submissions/799c955d-a657-4323-87b3-8b6832516371

-- Sol generated from Algebra/A4ForkPinning/MultiFactor.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Definitions.Def_Algebra_A4ForkPinning_MultiFactor
import Definitions.Def_Algebra_A4ForkPinning_Semiprime
import Theorems.Thm_A4ForkPinning_hb_zero
import Theorems.Thm_A4ForkPinning_info_leak
/-
# The order-3 channel for `k` factors, and its collapse

The semiprime laws of `Semiprime.lean` are the case `k = 2` of a family.  Let
`N = p₁⋯p_{k+1}` be a product of `k+1` unramified primes of the `A₄`-field; the
dial `N mod 9` sees only the sum `s = Σ chi9(pᵢ) ∈ ℤ/3` of the cube classes.

* `A4ForkPinning.card_fiber_sum` — every fibre of the sum map
  `(ℤ/3)^{k+1} → ℤ/3` has exactly `3^k` points (proved by an explicit bijection);
* `A4ForkPinning.allSplitRate_eq_count` — hence `P(all factors split | s) = 3^{-k}`
  if `s = 0` and `0` otherwise: the "all split" fork is the `3^{-k}`-thinning of
  the pinned fork `[s = 0]`;
* `A4ForkPinning.info_all_split` — **the `k`-factor AND law**
  `I = H(3^{-(k+1)}) - (1/3)·H(3^{-k})`, generalising the semiprime value
  `H(1/9) - (1/3)H(1/3)`;
* `A4ForkPinning.info_all_split_strict` — it is a genuine leak: `0 < I < H(F)`;
* `A4ForkPinning.info_all_split_tendsto_zero` — **the channel collapses**:
  `I → 0` as the number of factors grows.  Quantitatively, the residue of a
  many-factor number tells one essentially nothing about its factors' splitting
  behaviour: the "factor-uselessness" of the pinned fork.
-/

open A4ForkPinning

open Finset

/-! ## Fibres of the sum map on `(ℤ/3)^{k+1}` -/



/-! ## The `k`-factor AND channel -/



theorem allSplit_pinned_part : ∀ i : Fin 3,
    (![1, 0, 0] : Fin 3 → ℝ) i = 0 ∨ (![1, 0, 0] : Fin 3 → ℝ) i = 1 := by
  intro i; fin_cases i <;> norm_num

theorem avg_allSplit_pinned_part : avg w3 (![1, 0, 0] : Fin 3 → ℝ) = 1 / 3 := by
  simp [avg, w3, Fin.sum_univ_three]

/-- **The `k`-factor AND law.**  For `N` a product of `k+1` unramified primes,
`I(N mod 9 ; all factors split) = H(3^{-(k+1)}) - (1/3)·H(3^{-k})`.
For `k = 1` this is the semiprime value `H(1/9) - (1/3)H(1/3)`. -/
theorem info_all_split (k : ℕ) :
    info w3 (allSplitRate k) = hb ((1 / 3 : ℝ) ^ (k + 1)) - (1 / 3) * hb ((1 / 3 : ℝ) ^ k) := by
  have h := info_leak w3 (![1, 0, 0] : Fin 3 → ℝ) ((1 / 3 : ℝ) ^ k) allSplit_pinned_part
  rw [avg_allSplit_pinned_part] at h
  rw [show (1 / 3 : ℝ) ^ k * (1 / 3) = (1 / 3 : ℝ) ^ (k + 1) by rw [pow_succ]] at h
  exact h


/-! ## Collapse of the channel -/

theorem continuous_nml : Continuous nml :=
  Real.continuous_negMulLog.div_const _

theorem continuous_hb : Continuous hb :=
  continuous_nml.add (continuous_nml.comp (continuous_const.sub continuous_id))



open A4ForkPinning in
theorem solution:
    Filter.Tendsto (fun k => info w3 (allSplitRate k)) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpow' : Filter.Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hpow.comp (Filter.tendsto_add_atTop_nat 1)
  have h1 : Filter.Tendsto (fun k : ℕ => hb ((1 / 3 : ℝ) ^ (k + 1))) Filter.atTop (nhds 0) := by
    have := (continuous_hb.tendsto 0).comp hpow'
    simpa [hb_zero] using this
  have h2 : Filter.Tendsto (fun k : ℕ => (1 / 3 : ℝ) * hb ((1 / 3 : ℝ) ^ k))
      Filter.atTop (nhds 0) := by
    have := (continuous_hb.tendsto 0).comp hpow
    have h3 : Filter.Tendsto (fun k : ℕ => hb ((1 / 3 : ℝ) ^ k)) Filter.atTop (nhds 0) := by
      simpa [hb_zero] using this
    simpa using h3.const_mul (1 / 3 : ℝ)
  have := h1.sub h2
  simpa [info_all_split] using this
