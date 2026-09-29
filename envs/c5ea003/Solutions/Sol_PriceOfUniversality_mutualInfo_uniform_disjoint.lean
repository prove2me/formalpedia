-- Prove2me | solution 1 for PriceOfUniversality.mutualInfo_uniform_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:17:49.462978+00:00
-- url     : https://prove2.me/submissions/5f225885-908a-4a94-bad9-976b2a717fb8

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
theorem solution[Nonempty Θ] {p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (hdisj : DisjointSupports p) :
    mutualInfo (fun _ => (Fintype.card Θ : ℝ)⁻¹) p = logb 2 (Fintype.card Θ) := by
  set c : ℝ := (Fintype.card Θ : ℝ)⁻¹ with hc
  have hcard : (0:ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
  have hcpos : 0 < c := by positivity
  set m := mixture (fun _ => c) p with hmdef
  -- on the support of `p θ`, the mixture is just `c * p θ`
  have hmix : ∀ (θ : Θ) (a : A), 0 < p θ a → m a = c * p θ a := by
    intro θ a hpa
    rw [hmdef, mixture]
    rw [Finset.sum_eq_single θ]
    · intro θ' _ hne
      rw [hdisj θ θ' a (Ne.symm hne) hpa, mul_zero]
    · intro h; exact absurd (mem_univ θ) h
  have hkl : ∀ θ : Θ, kl (p θ) m = logb 2 (Fintype.card Θ) := by
    intro θ
    have hterm : ∀ a : A,
        p θ a * logb 2 (p θ a / m a) = p θ a * logb 2 (Fintype.card Θ) := by
      intro a
      rcases eq_or_lt_of_le ((hp θ).nonneg a) with h | h
      · simp [← h]
      · rw [hmix θ a h]
        have : p θ a / (c * p θ a) = (Fintype.card Θ : ℝ) := by
          rw [hc]; field_simp
        rw [this]
    calc kl (p θ) m = ∑ a, p θ a * logb 2 (p θ a / m a) := rfl
      _ = ∑ a, p θ a * logb 2 (Fintype.card Θ) := Finset.sum_congr rfl fun a _ => hterm a
      _ = logb 2 (Fintype.card Θ) := by rw [← Finset.sum_mul, (hp θ).total, one_mul]
  rw [mutualInfo, ← hmdef]
  calc ∑ _θ : Θ, c * kl (p _θ) m = ∑ _θ : Θ, c * logb 2 (Fintype.card Θ) :=
        Finset.sum_congr rfl fun θ _ => by rw [hkl θ]
    _ = logb 2 (Fintype.card Θ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hc, Finset.card_univ]
        field_simp
