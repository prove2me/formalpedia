-- Prove2me | solution 1 for Logic.PhaseRoute.sum_triAlign_mul_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:19:40.523391+00:00
-- url     : https://prove2.me/submissions/f67b8c95-6039-4d02-9472-5f84b91a3fab

-- Sol generated from Logic/PhaseRouteTripleAlignment.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteTripleAlignment
/-
# Degree hierarchy: three-way alignment defeats every pairwise encoding

Two further structural results for the phase-encoding programme.

## 1. Window stability is automatic (`Reindex` section)

Every quantity of the finite-sample calculus (`avg`, `cov`, `varr`, `msse`,
`Rsq`) is invariant under an arbitrary relabelling `e : κ ≃ ι` of the sample
space.  Consequently an *exactly zero* degree-1 effect transfers across windows
with ratio exactly `1`; a measured cross/same ratio different from `1` is
therefore evidence about the estimator, never about a genuine degree-1 signal.

## 2. The degree hierarchy does not stop at `2`

On `G × G × G` (`G` any finite additive commutative group; take `G = ZMod p`)
consider the **three-way alignment** target

  `triAlign (a,b,c) = if a + b + c = 0 then 1 else 0`.

Then `cov_triAlign_pairwise_eq_zero` : *every* predictor built from arbitrary
functions of **pairs** of coordinates,

  `pairwise F G H (a,b,c) = F (a,b) + G (b,c) + H (a,c)`,

has covariance exactly `0` with the target — so the entire degree-`≤2` layer,
interaction encodings included, is blind to it, while the target is trivially
degree-`3` measurable (`Rsq_triAlign_self_eq_one`).

This is the sharp prediction for the next experimental round: if the residual
excess is a `k`-way joint alignment, then encodings of degree `< k` must return
*exactly* zero population gain, no matter how many primes are dialled in.
-/

open Logic.PhaseRoute

open Finset

/-! ### Relabelling invariance: window stability of exact statements -/


variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]







/-! ### Three-way alignment on a finite abelian group -/


variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]




omit [DecidableEq G] [AddCommGroup G] in
/-- Normal form for sums over the triple product. -/
lemma sum_triple_eq (f : G × G × G → ℝ) :
    (∑ x : G × G × G, f x) = ∑ a : G, ∑ b : G, ∑ c : G, f (a, b, c) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _







/-! Lifting functions of two coordinates to the triple product. -/

















open Logic.PhaseRoute in
theorem solution(F : G × G → ℝ) :
    (∑ x : G × G × G, triAlign x * F (x.1, x.2.1)) = ∑ a : G, ∑ b : G, F (a, b) := by
  rw [sum_triple_eq]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (-(a + b))]
  · simp only [triAlign]
    split_ifs with hif
    · ring
    · exfalso
      apply hif
      show a + b + -(a + b) = 0
      abel
  · intro c _ hc
    have hne : ¬ (a + b + c = 0) := fun h => hc (by linear_combination (norm := abel) h)
    simp [triAlign, hne]
  · intro hmem
    exact absurd (Finset.mem_univ (-(a + b))) hmem
