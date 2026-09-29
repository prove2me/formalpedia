-- Prove2me | solution 1 for AffineStats.cnt_colSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:38:46.506983+00:00
-- url     : https://prove2.me/submissions/c1aaf982-ea75-4ccd-baeb-0c610afade9d

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_pt_injective
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
theorem solution(m : ℕ) (g : Vec n → Fin (m + 1)) (c : Vec n) {v : Fin d → Vec n}
    (hv : Indep v) :
    cnt (colSet m g) c v = ((cubeSet c v).filter fun x => g x = 0).card := by
  classical
  rw [cnt]
  refine Finset.card_nbij (fun y => pt c v y) ?_ ?_ ?_
  · intro y hy
    have hy' : pt c v y ∈ colSet m g := (mem_filter.mp hy).2
    have hg0 : g (pt c v y) = 0 := by
      simpa [colSet] using hy'
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨Finset.mem_image_of_mem _ (mem_univ y), hg0⟩
  · intro y _ y' _ h
    exact pt_injective c hv h
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, cubeSet, Finset.mem_image, mem_univ,
      true_and] at hx
    obtain ⟨⟨y, hy⟩, hgx⟩ := hx
    refine ⟨y, ?_, hy⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and, colSet, mem_filter]
    rw [hy]
    exact hgx
