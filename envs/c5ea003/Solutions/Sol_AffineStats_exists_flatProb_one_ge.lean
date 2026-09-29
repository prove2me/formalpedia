-- Prove2me | solution 1 for AffineStats.exists_flatProb_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:43:05.912987+00:00
-- url     : https://prove2.me/submissions/fd00f772-22ad-41d4-8177-c6021c5bba5a

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_card_indepParams_ge
import Theorems.Thm_AffineStats_exists_colouring_hitSet_ge
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the random construction for `s = 1`

This file continues the development of
`Catalog/Applications/AffineSubspaceStats/AffineStats.lean`, where the model
(random affine `d`-cubes in `𝔽₂ⁿ`, the statistic `cnt`, the probability `flatProb`)
is set up.

The paper's `s = 1` regime is governed by a *random* construction: keep each point of
`𝔽₂ⁿ` independently with probability `p`.  A `d`-flat `F` has `2^d` points, so it meets
such a random set in exactly one point with probability `2^d · p · (1-p)^{2^d - 1}`,
which is maximised at `p = 2^{-d}`, giving `(1 - 2^{-d})^{2^d - 1} → e^{-1}`.

We formalise this as a *counting* argument (no measure theory): instead of a random
subset we average over the `(m+1)^{2ⁿ}` colourings `g : 𝔽₂ⁿ → Fin (m+1)` and take
`A = g⁻¹(0)`, which realises `p = 1/(m+1)` exactly.  The combinatorial heart is
`AffineStats.card_exactly_one`: for a fixed set `T` of `t` points, exactly
`t · m^{t-1} · (m+1)^{|α| - t}` colourings vanish at exactly one point of `T`.

The main results are

* `AffineStats.exists_flatProb_one_ge` :
  `∃ A, λ(d+1,1) ≥ (2^{d+1}·m^{2^{d+1}-1} / (m+1)^{2^{d+1}}) · (1 - (2^{d+1}-1)/2ⁿ)`
  for every `m`;
* `AffineStats.exists_flatProb_one_ge_opt` : the choice `m + 1 = 2^{d+1}`, giving
  `λ(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1} · (1 - (2^{d+1}-1)/2ⁿ)`;
* `AffineStats.maxFlatProb_one_ge_limit` : hence
  `λ*(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1}`, which for `d = 0` is the exact value `1/2`
  and for every `d` beats the algebraic construction of
  `Catalog/Applications/AffineSubspaceStats/ExactProduct.lean` (e.g. `27/64` versus
  `3/8` for `2`-flats).
-/

open AffineStats

open Finset


variable {α : Type*} [Fintype α] [DecidableEq α]






variable {n d : ℕ}





















open Filter





open AffineStats in
theorem solution(n d m : ℕ) (hdn : d + 1 ≤ n) :
    ∃ A : Finset (Vec n),
      ((2 : ℚ) ^ (d + 1) * m ^ (2 ^ (d + 1) - 1) / (m + 1) ^ (2 ^ (d + 1)))
          * (1 - (2 ^ (d + 1) - 1) / 2 ^ n) ≤ flatProb n (d + 1) A 1 := by
  classical
  obtain ⟨g, hg⟩ := exists_colouring_hitSet_ge n d m
  refine ⟨colSet m g, ?_⟩
  set X := ((hitSet n (d + 1) (colSet m g) 1).card : ℚ) with hX
  set IP := ((univ.filter fun p : Param n (d + 1) => Indep p.2).card : ℚ) with hIP
  set R := (2 : ℚ) ^ (d + 1) * (m : ℚ) ^ (2 ^ (d + 1) - 1)
      / ((m : ℚ) + 1) ^ (2 ^ (d + 1)) with hR
  set K := ((m : ℚ) + 1) ^ (2 ^ n) with hK
  have hRnonneg : 0 ≤ R := by rw [hR]; positivity
  have hKpos : (0 : ℚ) < K := by rw [hK]; positivity
  have hpowsplit : K = ((m : ℚ) + 1) ^ (2 ^ n - 2 ^ (d + 1)) * ((m : ℚ) + 1) ^ (2 ^ (d + 1)) := by
    rw [hK, ← pow_add, Nat.sub_add_cancel (Nat.pow_le_pow_right (by norm_num) hdn)]
  -- the counting inequality, cast to `ℚ`
  have hcast : IP * ((2 : ℚ) ^ (d + 1)
      * ((m : ℚ) ^ (2 ^ (d + 1) - 1) * ((m : ℚ) + 1) ^ (2 ^ n - 2 ^ (d + 1)))) ≤ K * X := by
    have h := (Nat.cast_le (α := ℚ)).mpr hg
    push_cast at h
    rw [hX, hIP, hK]
    exact h
  have hCRK : ((2 : ℚ) ^ (d + 1)
      * ((m : ℚ) ^ (2 ^ (d + 1) - 1) * ((m : ℚ) + 1) ^ (2 ^ n - 2 ^ (d + 1)))) = R * K := by
    rw [hR, hpowsplit]
    have hne : (((m : ℚ) + 1) ^ (2 ^ (d + 1))) ≠ 0 := by positivity
    field_simp
  rw [hCRK] at hcast
  have hXge : IP * R ≤ X := by
    refine le_of_mul_le_mul_left ?_ hKpos
    calc K * (IP * R) = IP * (R * K) := by ring
      _ ≤ K * X := hcast
  -- the fraction of nondegenerate parameters
  have hcastsub : ((2 ^ (d + 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (d + 1) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  have hIPge : (2 : ℚ) ^ (n * (d + 1 + 1)) - ((2 : ℚ) ^ (d + 1) - 1) * 2 ^ (n * (d + 1)) ≤ IP := by
    have h := (Nat.cast_le (α := ℚ)).mpr (card_indepParams_ge n d)
    push_cast [hcastsub] at h
    rw [hIP]
    linarith
  -- assemble
  rw [flatProb, ← hX]
  have hPpos : (0 : ℚ) < 2 ^ (n * (d + 1 + 1)) := by positivity
  rw [le_div_iff₀ hPpos]
  have hsplit : (2 : ℚ) ^ (n * (d + 1 + 1)) = 2 ^ (n * (d + 1)) * 2 ^ n := by
    rw [← pow_add]; congr 1
  have hEeq : R * (1 - ((2 : ℚ) ^ (d + 1) - 1) / 2 ^ n) * 2 ^ (n * (d + 1 + 1))
      = R * (2 ^ (n * (d + 1 + 1)) - ((2 : ℚ) ^ (d + 1) - 1) * 2 ^ (n * (d + 1))) := by
    rw [mul_assoc]
    congr 1
    rw [hsplit]
    field_simp
  rw [hEeq]
  calc R * ((2 : ℚ) ^ (n * (d + 1 + 1)) - ((2 : ℚ) ^ (d + 1) - 1) * 2 ^ (n * (d + 1)))
      ≤ R * IP := mul_le_mul_of_nonneg_left hIPge hRnonneg
    _ = IP * R := by ring
    _ ≤ X := hXge
