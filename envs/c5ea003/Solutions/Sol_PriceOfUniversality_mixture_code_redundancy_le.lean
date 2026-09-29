-- Prove2me | solution 1 for PriceOfUniversality.mixture_code_redundancy_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:13:57.873138+00:00
-- url     : https://prove2.me/submissions/5a06b1d7-b224-4806-ac37-94647bf62926

-- Sol generated from Novelty/UniversalRedundancyMinimax.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
/-
# The price of universality, II: minimax redundancy and mutual information

A *universal* code must serve every source in a class `{p θ}` with a single
length function `L`, whereas a *specialised* code may be tuned to one source.
The number of extra bits this costs is the **price of universality**.

Main results of this file, for a finite class `Θ` of sources on a finite
alphabet `A`:

* `kl_compensation` — the exact decomposition
  `∑ θ, π θ * D(p θ ‖ q) = I(π) + D(mixture ‖ q)`, valid for every coding
  distribution `q`. This is the algebraic heart of the redundancy-capacity
  theorem.
* `exists_source_redundancy_ge_mutualInfo` — **lower bound**: whatever code is
  used, some source in the class pays at least the mutual information `I(π)`
  of any prior `π`.
* `price_of_universality_upper` — **upper bound**: the Shannon code built from
  the mixture pays at most `log₂ |Θ| + 1` bits on *every* source of the class.
* `price_of_universality_sandwich` — for a class of `m` sources with pairwise
  disjoint supports the minimax redundancy is exactly `log₂ m`, up to one bit:
  `log₂ m ≤ minimax redundancy ≤ log₂ m + 1`.

The last statement is the promised closed form: the price of universality over
a class of `m` mutually distinguishable sources is `log₂ m` bits, i.e. exactly
the number of bits needed to name the source — no more and no less.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] {Θ : Type*} [Fintype Θ]

/-! ## Mixtures and mutual information -/






/-! ## The compensation identity -/


/-! ## The lower bound: universality costs at least the mutual information -/



/-! ## The upper bound: the mixture code -/




/-! ## Exact price for a class of mutually distinguishable sources -/





open PriceOfUniversality in
theorem solution{p : A → ℝ} (hp : IsPMF p) {m : A → ℝ}
    (hmpos : ∀ a, 0 < m a) (hm1 : ∀ a, m a ≤ 1) :
    redundancy p (shannonCode m) ≤ kl p m + 1 := by
  have hlen : ∀ a : A, (shannonCode m a : ℝ) ≤ -logb 2 (m a) + 1 := by
    intro a
    have h : (0:ℝ) ≤ -logb 2 (m a) := by
      have := Real.logb_nonpos (b := 2) (by norm_num) (hmpos a).le (hm1 a)
      linarith
    exact (Nat.ceil_lt_add_one h).le
  have hstep : expLen p (shannonCode m) ≤ ∑ a, p a * (-logb 2 (m a) + 1) :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hlen a) (hp.nonneg a)
  have hexpand : ∑ a, p a * (-logb 2 (m a) + 1) = kl p m + entropy p + 1 := by
    have h1 : ∀ a : A, p a * (-logb 2 (m a) + 1)
        = (p a * logb 2 (p a / m a)) + (-(p a * logb 2 (p a))) + p a := by
      intro a
      rcases eq_or_lt_of_le (hp.nonneg a) with h | h
      · simp [← h]
      · rw [Real.logb_div (ne_of_gt h) (ne_of_gt (hmpos a))]; ring
    calc ∑ a, p a * (-logb 2 (m a) + 1)
        = ∑ a, ((p a * logb 2 (p a / m a)) + (-(p a * logb 2 (p a))) + p a) :=
          Finset.sum_congr rfl fun a _ => h1 a
      _ = (∑ a, p a * logb 2 (p a / m a)) + (∑ a, -(p a * logb 2 (p a)))
            + ∑ a, p a := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ = kl p m + entropy p + 1 := by rw [hp.total, kl, entropy]
  rw [redundancy]
  linarith
