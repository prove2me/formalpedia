-- Prove2me | solution 1 for Logic.PhaseRoute.avg_triAlign_mul_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:22:39.878775+00:00
-- url     : https://prove2.me/submissions/7f1d2682-0749-4e78-8d50-042a09892708

-- Sol generated from Logic/PhaseRouteTripleAlignment.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares
import Definitions.Def_Logic_PhaseRouteTripleAlignment
import Theorems.Thm_Logic_PhaseRoute_sum_triAlign_mul_fst_snd
import Theorems.Thm_Logic_PhaseRoute_sum_triAlign_mul_fst_thd
import Theorems.Thm_Logic_PhaseRoute_sum_triAlign_mul_snd_thd
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








/-! Lifting functions of two coordinates to the triple product. -/

















open Logic.PhaseRoute in
theorem solution(F H₂ H₃ : G × G → ℝ) :
    avg (fun x : G × G × G => triAlign x * pairwise F H₂ H₃ x)
      = ((∑ a : G, ∑ b : G, F (a, b)) + (∑ b : G, ∑ c : G, H₂ (b, c))
          + ∑ a : G, ∑ c : G, H₃ (a, c)) / ((Fintype.card G : ℝ) ^ 3) := by
  have hG := cardG_pos (G := G)
  have hs : (∑ x : G × G × G, triAlign x * pairwise F H₂ H₃ x)
      = (∑ a : G, ∑ b : G, F (a, b)) + (∑ b : G, ∑ c : G, H₂ (b, c))
          + ∑ a : G, ∑ c : G, H₃ (a, c) := by
    have hsplit : (fun x : G × G × G => triAlign x * pairwise F H₂ H₃ x)
        = fun x : G × G × G => (triAlign x * F (x.1, x.2.1)
            + triAlign x * H₂ (x.2.1, x.2.2)) + triAlign x * H₃ (x.1, x.2.2) := by
      funext x; simp only [pairwise]; ring
    rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_triAlign_mul_fst_snd,
      sum_triAlign_mul_snd_thd, sum_triAlign_mul_fst_thd]
  simp only [avg, hs, Fintype.card_prod, Nat.cast_mul]
  field_simp
