-- Prove2me | solution 1 for AffineStats.cnt_hyp_of_exists
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:40:42.115733+00:00
-- url     : https://prove2.me/submissions/ef4792a7-cb4c-4190-8983-2ecb69bd3e37

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_card_filter_involutive
import Theorems.Thm_AffineStats_pt_apply
import Theorems.Thm_AffineStats_sum_update_flip
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Affine subspace statistics in `𝔽₂ⁿ` : parity bounds

Motivated by the *affine subspace statistics problem* (the maximum, over `A ⊆ 𝔽₂ⁿ`, of
`P[|F ∩ A| = s]` for a uniformly random `d`-flat `F`), this file develops a fully finite,
self-contained model of the problem and proves sharp bounds for the *parity* statistic.

## The model

Instead of sampling a `d`-flat directly we sample an affine map `𝔽₂^d → 𝔽₂ⁿ`: a base point
`c` and direction vectors `v₀, …, v_{d-1}`, all uniform and independent. The associated
"affine `d`-cube" is the multiset `{c + ∑ yᵢ vᵢ : y ∈ 𝔽₂^d}` and
`cnt A c v = #{y : c + ∑ yᵢ vᵢ ∈ A}` is the number of its points (with multiplicity) in `A`.
When `v₀, …, v_{d-1}` are linearly independent — which happens with probability
`1 - O(2^{d-n})` — the cube is exactly a `d`-flat and `cnt A c v = |F ∩ A|`. Hence all
`n → ∞` limits of the two models agree, and this model is the convenient one for finite
combinatorial arguments.

## Main results

* `AffineStats.sum_cnt` : the first moment, `E[cnt] = 2^d · |A| / 2ⁿ`.
* `AffineStats.flatProb_compl` : the duality `λ(d, s) = λ(d, 2^d - s)` obtained by
  complementing `A`.
* `AffineStats.oddProb_le_half` : **the parity bound.** For every `n`, every `d ≥ 1` and
  every `A ⊆ 𝔽₂ⁿ`, the probability that a random affine `d`-cube meets `A` in an odd
  number of points is at most `1/2`.
* `AffineStats.flatProb_le_half_of_odd` : consequently `λ(d, s) ≤ 1/2` for every *odd* `s`.
* `AffineStats.exists_oddProb_ge` : the bound `1/2` is asymptotically attained; averaging
  over all `A` produces a set with odd-intersection probability `≥ 1/2 - (2^d-1)/2^{n+1}`.
* `AffineStats.tendsto_maxOddProb` : hence `maxₐ P[|F ∩ A| odd] → 1/2` as `n → ∞`.
* `AffineStats.hyperplane_flatProb` : for the hyperplane `A = {x : x₀ = 0}` one has
  `P[|F ∩ A| = 2^{d-1}] = 1 - 2^{-d}` *exactly*; this is the `k = d-1` case of the
  standard lower-bound construction `λ*(d, j·2^k) ≥ 1 - 2^{-k}`.
* `AffineStats.exists_flatProb_gt_half` : the parity bound does **not** extend to even `s`.
* `AffineStats.tendsto_maxFlatProb_one` : `λ*(1, 1) = 1/2`, the `d = 1` instance of the
  exact determination of `λ*(d, 1)`.
* `AffineStats.flatProb_univ` : at `s = 2^d` the value is `1`, so the regime `s < 2^d` is
  essential in the formula `λ*(d, j·2^k) = 1 - 2^{-k}`.
* `AffineStats.maxOddProb_dim2_lt_half` : at `n = d = 2` the bound `1/2` is not attained,
  so `1/2` is a genuine limit rather than a finite-`n` maximum.
-/

open AffineStats

open Finset










variable {n d : ℕ}











/-- Flipping one coordinate of a vector of `𝔽₂^d` is an involution. -/
lemma flip_involutive (i₀ : Fin d) :
    Function.Involutive (fun y : Fin d → ZMod 2 => Function.update y i₀ (y i₀ + 1)) := by
  intro y
  funext i
  by_cases hii : i = i₀ <;>
    simp [hii, Function.update_apply, add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl]




variable {n d : ℕ}





variable {n d : ℕ}





variable {n d : ℕ}









variable {n d : ℕ}







































open AffineStats in
theorem solution{n d : ℕ} (c : Vec (n + 1)) (v : Fin (d + 1) → Vec (n + 1))
    (h : ∃ i, v i 0 = 1) : cnt (hyp n) c v = 2 ^ d := by
  obtain ⟨i₀, hi₀⟩ := h
  have key := card_filter_involutive (α := Fin (d + 1) → ZMod 2)
    (P := fun y => pt c v y ∈ hyp n)
    (g := fun y => Function.update y i₀ (y i₀ + 1)) (flip_involutive i₀)
    (by
      intro y
      simp only [hyp, Finset.mem_filter, Finset.mem_univ, true_and, pt_apply]
      rw [sum_update_flip y i₀ (fun i => v i 0), hi₀, ← add_assoc]
      generalize (c 0 + ∑ i, y i * v i 0) = t
      revert t
      decide)
  rw [cnt]
  have hc : Fintype.card (Fin (d + 1) → ZMod 2) = 2 ^ (d + 1) := by simp
  rw [hc] at key
  omega
