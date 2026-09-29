-- Prove2me | solution 1 for AffineStats.oddProb_le_half
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:52:50.876993+00:00
-- url     : https://prove2.me/submissions/615963d9-a93a-483f-aa44-633e7eba2b01

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_key_pair_bound
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

/-- Splitting the affine `(d+1)`-cube into the two parallel `d`-cubes obtained by fixing
the first coordinate of `y`. -/
lemma cnt_succ (A : Finset (Vec n)) (c : Vec n) (v : Fin (d + 1) → Vec n) :
    cnt A c v = cnt A c (fun i => v i.succ) + cnt A (c + v 0) (fun i => v i.succ) := by
  simp only [cnt_eq_sum]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => ZMod 2))
      (fun q => if pt c v (Fin.cons q.1 q.2) ∈ A then 1 else 0)
      (fun y => if pt c v y ∈ A then 1 else 0) (fun q => by rfl)]
  rw [Fintype.sum_prod_type]
  have h2 : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [h2]
  simp [pt, Fin.sum_univ_succ, add_assoc]








variable {n d : ℕ}







































open AffineStats in
theorem solution(n d : ℕ) (A : Finset (Vec n)) : oddProb n (d + 1) A ≤ 1 / 2 := by
  classical
  set f : Vec n → Vec n → (Fin d → Vec n) → ℕ :=
    fun c a w => if ¬ (2 ∣ (cnt A c w + cnt A (c + a) w)) then 1 else 0 with hf
  have hL : (oddSet n (d + 1) A).card
      = ∑ c : Vec n, ∑ a : Vec n, ∑ w : Fin d → Vec n, f c a w := by
    simp only [oddSet, Finset.card_filter]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => Vec n))
        (fun q => if ¬ (2 ∣ cnt A c (Fin.cons q.1 q.2)) then 1 else 0)
        (fun v => if ¬ (2 ∣ cnt A c v) then 1 else 0) (fun q => by rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun w _ => ?_))
    rw [cnt_succ]
    simp [hf]
  have hsum : (oddSet n (d + 1) A).card = ∑ w : Fin d → Vec n,
      (univ.filter fun p : Vec n × Vec n =>
        ¬ (2 ∣ (cnt A p.1 w + cnt A (p.1 + p.2) w))).card := by
    rw [hL]
    rw [show (∑ c : Vec n, ∑ a : Vec n, ∑ w : Fin d → Vec n, f c a w)
        = ∑ c : Vec n, ∑ w : Fin d → Vec n, ∑ a : Vec n, f c a w from
      Finset.sum_congr rfl (fun c _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.card_filter, Fintype.sum_prod_type]
  have hbound : 2 * (oddSet n (d + 1) A).card ≤ 2 ^ (n * (d + 2)) := by
    rw [hsum, Finset.mul_sum]
    calc ∑ w : Fin d → Vec n, 2 * (univ.filter fun p : Vec n × Vec n =>
            ¬ (2 ∣ (cnt A p.1 w + cnt A (p.1 + p.2) w))).card
        ≤ ∑ _w : Fin d → Vec n, 2 ^ (2 * n) :=
          Finset.sum_le_sum (fun w _ => key_pair_bound A w)
      _ = 2 ^ (n * d) * 2 ^ (2 * n) := by
          simp [Finset.card_univ, ZMod.card, ← pow_mul, mul_comm]
      _ = 2 ^ (n * (d + 2)) := by rw [← pow_add]; ring_nf
  rw [oddProb, div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (n * (d + 1 + 1)))]
  have h2 : ((2 : ℚ) * (oddSet n (d + 1) A).card) ≤ 2 ^ (n * (d + 2)) := by
    exact_mod_cast hbound
  have h3 : n * (d + 1 + 1) = n * (d + 2) := by ring
  rw [h3]
  linarith
