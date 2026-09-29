-- Prove2me | solution 1 for PriceOfUniversality.kl_compensation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:37.677769+00:00
-- url     : https://prove2.me/submissions/6a795327-fdf4-4c1d-995f-fe42968eafed

-- Sol generated from Novelty/UniversalRedundancyMinimax.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Theorems.Thm_PriceOfUniversality_mixture_pos
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
theorem solution{pri : Θ → ℝ} {p : Θ → A → ℝ} {q : A → ℝ}
    (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
    (hq : ∀ a, 0 < q a) :
    ∑ θ, pri θ * kl (p θ) q = mutualInfo pri p + kl (mixture pri p) q := by
  set m := mixture pri p with hm
  have hmpos : ∀ θ : Θ, ∀ a : A, 0 < p θ a → 0 < m a := by
    intro θ a hpa
    exact mixture_pos hpri.nonneg hp (hpripos θ) hpa
  -- pointwise splitting of the log-ratio
  have hsplit : ∀ (θ : Θ) (a : A),
      p θ a * logb 2 (p θ a / q a)
        = p θ a * logb 2 (p θ a / m a) + p θ a * logb 2 (m a / q a) := by
    intro θ a
    rcases eq_or_lt_of_le ((hp θ).nonneg a) with h | h
    · simp [← h]
    · have hma : 0 < m a := hmpos θ a h
      rw [Real.logb_div (ne_of_gt h) (ne_of_gt (hq a)),
        Real.logb_div (ne_of_gt h) (ne_of_gt hma),
        Real.logb_div (ne_of_gt hma) (ne_of_gt (hq a))]
      ring
  have step1 : ∀ θ : Θ, kl (p θ) q
      = kl (p θ) m + ∑ a, p θ a * logb 2 (m a / q a) := by
    intro θ
    rw [kl, kl, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => hsplit θ a
  have step2 : ∑ θ, pri θ * (∑ a, p θ a * logb 2 (m a / q a)) = kl m q := by
    rw [kl]
    have : ∀ θ : Θ, pri θ * (∑ a, p θ a * logb 2 (m a / q a))
        = ∑ a, (pri θ * p θ a) * logb 2 (m a / q a) := by
      intro θ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_congr rfl fun θ _ => this θ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]
    rfl
  calc ∑ θ, pri θ * kl (p θ) q
      = ∑ θ, (pri θ * kl (p θ) m + pri θ * (∑ a, p θ a * logb 2 (m a / q a))) := by
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [step1 θ]; ring
    _ = (∑ θ, pri θ * kl (p θ) m) + ∑ θ, pri θ * (∑ a, p θ a * logb 2 (m a / q a)) :=
        Finset.sum_add_distrib
    _ = mutualInfo pri p + kl m q := by rw [step2]; rfl
