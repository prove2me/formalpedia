-- Prove2me | solution 1 for Catalog.Novelty.CoverDichotomy.coverCount_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:58:54.541169+00:00
-- url     : https://prove2.me/submissions/bac86a51-7a3a-42a0-99a8-5853d6adf4ef

-- Sol generated from Novelty/CoverDichotomyCount.lean
import Mathlib
import Definitions.Def_Novelty_CoverDichotomyCount

/-!
# Cover's counting function and manifold-constrained dichotomy bounds

For `N` points in *general position* in a `d`-parameter space, the number of
homogeneously linearly-separable dichotomies is **Cover's counting function**

  `C(N, d) = 2 · Σ_{k = 0}^{d-1} binom(N-1, k)`

(Cover, *Geometrical and Statistical Properties of Systems of Linear
Inequalities…*, 1965). This file develops the combinatorial theory of
`coverCount` and packages the **manifold-constrained dichotomy bound**:

For a `d`-dimensional submanifold `E ⊂ ℝ^M` and a smooth injective
`Φ : E → ℝ^{M'}`, points of `E` in general position have Kruskal rank
`s ≤ d + 1`, and the Φ-separable dichotomy count `C_F(N)` obeys the same
one-point recursion as Cover's function with parameter budget `p = d + M' + 1`.
The `DichotomySystem` structure abstracts exactly that geometric recursion, and
we prove that **any** quantity obeying it is bounded by `coverCount N p`, hence
by `2^N`, *strictly* below `2^N` once `p < N` — the loss of expressivity forced
by low-dimensional data structure.

## Main results

* `coverCount_recurrence`      — the Cover / Pascal one-point recurrence;
* `coverCount_saturate`        — `C(N,d) = 2^N` when the budget dominates (`N ≤ d`);
* `coverCount_lt_two_pow`      — strict collapse `C(N,d) < 2^N` when `d < N`;
* `coverCount_maximal_solution`— Cover's function is the maximal solution of the
  recursion (the analytic heart);
* `DichotomySystem.count_le_coverCount` — the manifold-constrained bound;
* `DichotomySystem.count_lt_two_pow`    — strict expressivity collapse.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): Cover's function is the *maximal* solution of the
geometric one-point recursion `C(N+1,d+1) ≤ C(N,d+1)+C(N,d)` with base values
`2`; a low parameter budget `p = d+M'+1 < N` must strictly depress the dichotomy
count below `2^N`. Surprising sub-claim: the manifold's *intrinsic* dimension
`d`, not the ambient `M`, controls the bound — an `M`-independent statement.

EXPERIMENT (Experimenter): `#eval` on `coverCount` (see ComputationalEvidence.md)
confirms saturation `C(N,d)=2^N` for `N≤d`, strict collapse for `d<N`
(`C(5,3)=22<32`), the recurrence for all `N≥1`, and that the recurrence *fails*
at `N=0` — pinning the `1 ≤ N` side conditions.

ANALYSIS (Analyst): the recurrence and saturation are finite binomial-sum
identities (`Nat.sum_range_choose`, `Finset.sum_range_succ`, Pascal via
`Nat.choose_succ_succ'`). The genuine content is `coverCount_maximal_solution`:
a two-parameter induction (`Nat.le_induction` on `N`, case split on `d`) that
turns the *geometric* recursion into the *closed-form* binomial bound. This is
the exact skeleton of Cover's theorem — the recursion is the geometry, the
closed form is combinatorics.

CRITIQUE (Critic): is the `DichotomySystem` abstraction vacuous? No — the
instance `coverCountSystem` satisfies every hypothesis with equality, so the
bound `count ≤ coverCount` is *tight* and the structure is inhabited. The strict
collapse theorem is not vacuous either: it produces the concrete separation
`C(N,p) < 2^N` whenever `p < N`.
-- !-- end Lab Notes -- !--
-/

open Catalog.Novelty.CoverDichotomy

open Finset



















open Catalog.Novelty.CoverDichotomy in
theorem solution{N d : ℕ} (hd : d < N) :
    coverCount N d < 2 ^ N := by
  unfold coverCount
  have hsub : ∑ k ∈ range d, (N - 1).choose k ≤ ∑ k ∈ range (N - 1), (N - 1).choose k :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have hfull : ∑ k ∈ range ((N - 1) + 1), (N - 1).choose k = 2 ^ (N - 1) :=
    Nat.sum_range_choose (N - 1)
  rw [Finset.sum_range_succ, Nat.choose_self] at hfull
  have hpow : 2 ^ (N - 1) * 2 = 2 ^ N := by rw [← pow_succ]; congr 1; omega
  omega
