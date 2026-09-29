-- Prove2me | Definitions.Def_Applications_AffineSubspaceStats_AffineStats
-- name    : Applications_AffineSubspaceStats_AffineStats
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:26.958274+00:00
-- url     : https://prove2.me/theorems/817a7e83-5b10-4e6e-b568-78980340bb86
-- title:
--   Aether Catalog definitions — Applications_AffineSubspaceStats_AffineStats
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AffineSubspaceStats.AffineStats`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AffineSubspaceStats/AffineStats.lean by skeleton subtraction
import Mathlib
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

namespace AffineStats

open Finset

/-- The ambient space `𝔽₂ⁿ`. -/
abbrev Vec (n : ℕ) : Type := Fin n → ZMod 2

/-- The parameter space of affine `d`-cubes: a base point together with `d` directions. -/
abbrev Param (n d : ℕ) : Type := Vec n × (Fin d → Vec n)

/-- The point of the affine cube with base point `c` and directions `v` indexed by
`y ∈ 𝔽₂^d`. -/
def pt {n d : ℕ} (c : Vec n) (v : Fin d → Vec n) (y : Fin d → ZMod 2) : Vec n :=
  c + ∑ i, y i • v i

/-- The number of points of the affine cube `(c, v)` lying in `A`. -/
def cnt {n d : ℕ} (A : Finset (Vec n)) (c : Vec n) (v : Fin d → Vec n) : ℕ :=
  (univ.filter fun y : Fin d → ZMod 2 => pt c v y ∈ A).card

/-- The set of parameters whose cube meets `A` in exactly `s` points. -/
def hitSet (n d : ℕ) (A : Finset (Vec n)) (s : ℕ) : Finset (Param n d) :=
  univ.filter fun p => cnt A p.1 p.2 = s

/-- The set of parameters whose cube meets `A` in an odd number of points. -/
def oddSet (n d : ℕ) (A : Finset (Vec n)) : Finset (Param n d) :=
  univ.filter fun p => ¬ (2 ∣ cnt A p.1 p.2)

/-- `P[|F ∩ A| = s]` for a uniformly random affine `d`-cube `F` in `𝔽₂ⁿ`. -/
def flatProb (n d : ℕ) (A : Finset (Vec n)) (s : ℕ) : ℚ :=
  ((hitSet n d A s).card : ℚ) / 2 ^ (n * (d + 1))

/-- `P[|F ∩ A| is odd]` for a uniformly random affine `d`-cube `F` in `𝔽₂ⁿ`. -/
def oddProb (n d : ℕ) (A : Finset (Vec n)) : ℚ :=
  ((oddSet n d A).card : ℚ) / 2 ^ (n * (d + 1))

section Basic

variable {n d : ℕ}













end Basic

section FirstMoment

variable {n d : ℕ}



end FirstMoment

section Duality

variable {n d : ℕ}



end Duality

section Parity

variable {n d : ℕ}







end Parity

section Sharpness

variable {n d : ℕ}

/-- Independence of the directions, stated concretely: no nontrivial `𝔽₂`-combination
vanishes. -/
def Indep {n d : ℕ} (v : Fin d → Vec n) : Prop :=
  ∀ y : Fin d → ZMod 2, y ≠ 0 → ∑ i, y i • v i ≠ 0

instance {n d : ℕ} (v : Fin d → Vec n) : Decidable (Indep v) := by
  unfold Indep; infer_instance











/-- The maximum, over subsets `A ⊆ 𝔽₂ⁿ`, of the odd-intersection probability. -/
def maxOddProb (n d : ℕ) : ℚ :=
  (univ : Finset (Finset (Vec n))).sup' ⟨∅, mem_univ _⟩ (fun A => oddProb n d A)




end Sharpness

section Hyperplane

/-- The coordinate hyperplane `{x : x₀ = 0}` of `𝔽₂^{n+1}`. -/
def hyp (n : ℕ) : Finset (Vec (n + 1)) := univ.filter fun x => x 0 = 0








end Hyperplane

section ExactCases

/-- The maximum of `P[|F ∩ A| = s]` over all `A ⊆ 𝔽₂ⁿ`. -/
def maxFlatProb (n d s : ℕ) : ℚ :=
  (univ : Finset (Finset (Vec n))).sup' ⟨∅, mem_univ _⟩ (fun A => flatProb n d A s)








end ExactCases

end AffineStats


