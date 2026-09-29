-- Prove2me | solution 1 for Logic.PhaseRoute.avg_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:19:40.018893+00:00
-- url     : https://prove2.me/submissions/cc923e2d-558f-4d84-aeed-9683bdbbea83

-- Sol generated from Logic/PhaseRouteTripleAlignment.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares
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



omit [DecidableEq G] in
lemma cardG_pos : (0:ℝ) < (Fintype.card G : ℝ) := by
  have : 0 < Fintype.card G := Fintype.card_pos
  positivity

omit [DecidableEq G] [AddCommGroup G] in
/-- Normal form for sums over the triple product. -/
lemma sum_triple_eq (f : G × G × G → ℝ) :
    (∑ x : G × G × G, f x) = ∑ a : G, ∑ b : G, ∑ c : G, f (a, b, c) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _







/-! Lifting functions of two coordinates to the triple product. -/

omit [DecidableEq G] [AddCommGroup G] in
lemma sum_lift_fst_snd (F : G × G → ℝ) :
    (∑ x : G × G × G, F (x.1, x.2.1))
      = (Fintype.card G : ℝ) * ∑ a : G, ∑ b : G, F (a, b) := by
  rw [sum_triple_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq G] [AddCommGroup G] in
lemma sum_lift_snd_thd (H₂ : G × G → ℝ) :
    (∑ x : G × G × G, H₂ (x.2.1, x.2.2))
      = (Fintype.card G : ℝ) * ∑ b : G, ∑ c : G, H₂ (b, c) := by
  rw [sum_triple_eq]
  have hconst : ∀ a : G, (∑ b : G, ∑ c : G, H₂ ((a, b, c).2.1, (a, b, c).2.2))
      = ∑ b : G, ∑ c : G, H₂ (b, c) := fun _ => rfl
  rw [Finset.sum_congr rfl fun a _ => hconst a, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

omit [DecidableEq G] [AddCommGroup G] in
lemma sum_lift_fst_thd (H₃ : G × G → ℝ) :
    (∑ x : G × G × G, H₃ (x.1, x.2.2))
      = (Fintype.card G : ℝ) * ∑ a : G, ∑ c : G, H₃ (a, c) := by
  rw [sum_triple_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]














open Logic.PhaseRoute in
omit [DecidableEq G] in
theorem solution(F H₂ H₃ : G × G → ℝ) :
    avg (pairwise F H₂ H₃)
      = ((∑ a : G, ∑ b : G, F (a, b)) + (∑ b : G, ∑ c : G, H₂ (b, c))
          + ∑ a : G, ∑ c : G, H₃ (a, c)) / ((Fintype.card G : ℝ) ^ 2) := by
  have hG := cardG_pos (G := G)
  have hs : (∑ x : G × G × G, pairwise F H₂ H₃ x)
      = (Fintype.card G : ℝ) *
        ((∑ a : G, ∑ b : G, F (a, b)) + (∑ b : G, ∑ c : G, H₂ (b, c))
          + ∑ a : G, ∑ c : G, H₃ (a, c)) := by
    simp only [pairwise]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_lift_fst_snd, sum_lift_snd_thd,
      sum_lift_fst_thd]
    ring
  simp only [avg, hs, Fintype.card_prod, Nat.cast_mul]
  field_simp
