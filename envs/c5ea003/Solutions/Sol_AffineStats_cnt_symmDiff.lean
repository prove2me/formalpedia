-- Prove2me | solution 1 for AffineStats.cnt_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:34:02.157231+00:00
-- url     : https://prove2.me/submissions/4e47e836-c26e-4681-b6f1-3771472b12c8

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
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






lemma cnt_eq_sum (A : Finset (Vec n)) (c : Vec n) (v : Fin d → Vec n) :
    cnt A c v = ∑ y : Fin d → ZMod 2, if pt c v y ∈ A then 1 else 0 := by
  rw [cnt, Finset.card_filter]









variable {n d : ℕ}





variable {n d : ℕ}





variable {n d : ℕ}









variable {n d : ℕ}







































open AffineStats in
theorem solution(c : Vec n) (v : Fin d → Vec n) (hinj : Function.Injective (pt c v))
    (A : Finset (Vec n)) :
    ∃ T : ℕ, cnt A c v + cnt (symmDiff A {pt c v 0}) c v = 1 + 2 * T := by
  classical
  set y₀ : Fin d → ZMod 2 := 0
  set p₀ := pt c v y₀ with hp₀
  set B := symmDiff A {p₀} with hB
  refine ⟨(univ.erase y₀).filter (fun y => pt c v y ∈ A) |>.card, ?_⟩
  have hA : cnt A c v
      = (∑ y ∈ univ.erase y₀, if pt c v y ∈ A then 1 else 0) + (if p₀ ∈ A then 1 else 0) := by
    rw [cnt_eq_sum]
    exact (Finset.sum_erase_add _ _ (mem_univ y₀)).symm
  have htail : ∀ y ∈ univ.erase y₀, (if pt c v y ∈ B then 1 else 0)
      = (if pt c v y ∈ A then 1 else 0) := by
    intro y hy
    have hne : pt c v y ≠ p₀ := fun h => (Finset.mem_erase.mp hy).1 (hinj h)
    have hiff : (pt c v y ∈ B) ↔ (pt c v y ∈ A) := by
      simp [hB, Finset.mem_symmDiff, hne]
    simp [hiff]
  have hBc : cnt B c v
      = (∑ y ∈ univ.erase y₀, if pt c v y ∈ A then 1 else 0) + (if p₀ ∈ B then 1 else 0) := by
    rw [cnt_eq_sum, ← Finset.sum_erase_add _ _ (mem_univ y₀)]
    rw [Finset.sum_congr rfl htail]
  have hhead : (if p₀ ∈ B then 1 else 0) + (if p₀ ∈ A then 1 else 0) = 1 := by
    by_cases h : p₀ ∈ A
    · have hnB : p₀ ∉ B := by simp [hB, Finset.mem_symmDiff, h]
      simp [hnB, h]
    · have hmB : p₀ ∈ B := by simp [hB, Finset.mem_symmDiff, h]
      simp [hmB, h]
  rw [hA, hBc, ← Finset.card_filter]
  omega
