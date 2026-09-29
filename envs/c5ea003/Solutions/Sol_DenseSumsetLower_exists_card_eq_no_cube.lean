-- Prove2me | solution 1 for DenseSumsetLower.exists_card_eq_no_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:50.994324+00:00
-- url     : https://prove2.me/submissions/71844d4b-9d3c-4b67-a5c1-5c66183f6040

-- Sol generated from Bridges/DenseSumsetLower/CubeSharp.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
import Definitions.Def_Bridges_DenseSumsetLower_CubeSharp
import Theorems.Thm_DeltaDense_exists_card_eq_avoiding_family
/-
# The matching upper bound for affine cubes in `δ`-dense subsets of `[n]`

`Bridges.DenseSumsetLower.Cube` proves the *existence* side of the multi-fold problem:
every `S ⊆ [0,n)` with `|S| ≥ δ n` contains an affine cube
`u + {0,a₁} + ⋯ + {0,a_d}` of dimension `d` as soon as `(4/δ)^{2^d} ≤ 2 n`, i.e. for every
`d ≤ log₂ (log (2n) / log (4/δ))`.

This file proves the opposite (first-moment) side: for `d` slightly *above* that range
there are `δ`-dense sets `S ⊆ [n]` containing **no** affine cube of dimension `d` with
`2^d` distinct elements.  A `d`-dimensional cube inside `[n]` is described by `d + 1`
parameters — the base point `u` and the generators `a₁, …, a_d` — so the union bound costs
`n^{d+1}` while each proper cube forces `2^d` points of `S`; the two balance at
`2^d ≈ (d+1)·log n / log (1/δ)`, i.e. at `d ≈ log₂ (log n / log (1/δ))`, the same order as
the existence threshold.

Contents:
* `DenseSumsetLower.funCube` — the affine cube `u + {0,a₁} + ⋯ + {0,a_d}` in `ℕ`, written
  as the set of subset sums of the generator family `f : Fin d → ℕ`;
* `DenseSumsetLower.exists_card_eq_no_cube` — the counting statement: if
  `n^{d+1}·m^L < n^L` then some `m`-element `S ⊆ [n]` contains no `d`-dimensional cube with
  at least `L` distinct elements;
* `DenseSumsetLower.cube_pow_cond` — the analytic form of `n^c·m^L < n^L` for
  `m = ⌈δ n⌉`, valid for **all** exponents `c` (unlike `DeltaDense.pow_cond`, which is
  restricted to `c ≤ 10`; here `c = d + 1` must be allowed to grow with `n`);
* `DenseSumsetLower.exists_dense_no_cube` and its asymptotic packaging
  `DenseSumsetLower.eventually_exists_dense_no_cube`;
* `DenseSumsetLower.cube_dimension_window` — the consistency of the two sides: for `n`
  large no dimension `d` satisfies both the existence condition `(4/δ)^{2^d} ≤ 2n` of
  `exists_cube_of_density_int` and the avoidance condition
  `(1+ε)(d+1)·log n ≤ 2^d·log (1/δ)` proved here, so the avoidance range of `d` begins
  strictly beyond the existence range.

Caveat on the shape of the two bounds: the avoidance statement is about *proper* cubes
(those with `2^d` distinct elements — equivalently, `L = 2^d` in the counting form, which
also covers every intermediate `L`), whereas the existence statement of `Cube.lean`
produces a cube with nonzero generators which need not be proper.  Upgrading the existence
side to proper cubes is exactly sub-conjecture 3 of `FUTURE_DIRECTIONS.md`.
-/

open DenseSumsetLower

open Finset DeltaDense

/-! ## Affine cubes in `ℕ` as sets of subset sums -/



/-- The base point belongs to the cube (take `T = ∅`). -/
lemma self_mem_funCube {d : ℕ} (u : ℕ) (f : Fin d → ℕ) : u ∈ funCube u f :=
  Finset.mem_image.2 ⟨∅, Finset.mem_univ _, by simp⟩

/-- Each generator gives a point of the cube (take `T = {i}`). -/
lemma add_mem_funCube {d : ℕ} (u : ℕ) (f : Fin d → ℕ) (i : Fin d) :
    u + f i ∈ funCube u f :=
  Finset.mem_image.2 ⟨{i}, Finset.mem_univ _, by simp⟩

/-! ## The counting statement -/


/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no proper cube of a given dimension -/





open DenseSumsetLower in
theorem solution{n m d L : ℕ} (hmn : m ≤ n) (hL : 1 ≤ L)
    (hcond : n ^ (d + 1) * m ^ L < n ^ L) :
    ∃ S ⊆ range n, S.card = m ∧
      ∀ (u : ℕ) (f : Fin d → ℕ), (∀ i, 0 < f i) → L ≤ (funCube u f).card →
        ¬ (funCube u f ⊆ S) := by
  classical
  set J : Finset (ℕ × (Fin d → ℕ)) :=
    (range n) ×ˢ (Fintype.piFinset fun _ : Fin d => Icc 1 n) with hJ
  set I : Finset (ℕ × (Fin d → ℕ)) := J.filter (fun p => L ≤ (funCube p.1 p.2).card) with hI
  have hJcard : J.card = n ^ (d + 1) := by
    rw [hJ, Finset.card_product, Fintype.card_piFinset, Finset.card_range]
    simp [Nat.card_Icc, pow_succ, mul_comm]
  have hIcard : I.card ≤ n ^ (d + 1) := by
    rw [← hJcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨S, hSsub, hScard, hSno⟩ :=
    exists_card_eq_avoiding_family I (fun p => funCube p.1 p.2)
      (fun p hp => by
        rw [hI, Finset.mem_filter] at hp
        exact hp.2)
      hmn hL
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ hIcard) hcond)
  refine ⟨S, hSsub, hScard, ?_⟩
  intro u f hf hcard hsub
  refine hSno (u, f) ?_ hsub
  rw [hI, Finset.mem_filter, hJ, Finset.mem_product, Fintype.mem_piFinset]
  refine ⟨⟨?_, ?_⟩, hcard⟩
  · simpa using hSsub (hsub (self_mem_funCube u f))
  · intro i
    have hmem : u + f i < n := by
      simpa using hSsub (hsub (add_mem_funCube u f i))
    show f i ∈ Icc 1 n
    exact Finset.mem_Icc.2 ⟨hf i, by omega⟩
