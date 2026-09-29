-- Prove2me | Definitions.Def_Novelty_CoverDichotomyCount
-- name    : Novelty_CoverDichotomyCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:07.324033+00:00
-- url     : https://prove2.me/theorems/d1fa7e29-c4ba-4319-bffb-b034e4e414ba
-- title:
--   Aether Catalog definitions — Novelty_CoverDichotomyCount
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CoverDichotomyCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CoverDichotomyCount.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Novelty.CoverDichotomy

open Finset

/-- **Cover's counting function** `C(N, d) = 2 · Σ_{k<d} binom(N-1, k)`: the
number of homogeneously linearly-separable dichotomies of `N` points in general
position in a `d`-parameter space. -/
def coverCount (N d : ℕ) : ℕ := 2 * ∑ k ∈ Finset.range d, (N - 1).choose k

/-- A single point admits both labels: `C(1, d) = 2` for `d ≥ 1`. -/
theorem coverCount_one_left {d : ℕ} (hd : 1 ≤ d) : coverCount 1 d = 2 := by
  unfold coverCount
  simp only [Nat.sub_self]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)
  · intro h; simp at h; omega

/-- A homogeneous threshold in one parameter: `C(N, 1) = 2`. -/
theorem coverCount_one_right (N : ℕ) : coverCount N 1 = 2 := by
  unfold coverCount; simp

/-- Partial-sum Pascal identity: `Σ_{k<d+1} binom(m+1,k) =
Σ_{k<d+1} binom(m,k) + Σ_{k<d} binom(m,k)`. -/
theorem sum_aux (m d : ℕ) :
    ∑ k ∈ range (d + 1), (m + 1).choose k
      = ∑ k ∈ range (d + 1), m.choose k + ∑ k ∈ range d, m.choose k := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ (f := fun k => (m + 1).choose k), ih,
        Finset.sum_range_succ (f := fun k => m.choose k) (n := d + 1),
        Finset.sum_range_succ (f := fun k => m.choose k) (n := d)]
    have : (m + 1).choose (d + 1) = m.choose d + m.choose (d + 1) := by
      rw [Nat.choose_succ_succ']
    omega



/-- **Cover / Pascal one-point recurrence.** For `N ≥ 1`,
`C(N+1, d+1) = C(N, d+1) + C(N, d)`. This is the combinatorial shadow of Cover's
geometric "add one point" argument. -/
theorem coverCount_recurrence {N : ℕ} (hN : 1 ≤ N) (d : ℕ) :
    coverCount (N + 1) (d + 1) = coverCount N (d + 1) + coverCount N d := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  unfold coverCount
  simp only [Nat.add_sub_cancel]
  rw [sum_aux m d]
  ring





/-- A **dichotomy system**: an abstract `count N p` (number of Φ-separable
dichotomies of `N` points with a `p`-parameter classifier) obeying Cover's
geometric one-point recursion and base values. The manifold-constrained setting
of the mission instantiates this with `p = d + M' + 1`. -/
structure DichotomySystem where
  /-- Number of realizable dichotomies of `N` points with budget `p`. -/
  count : ℕ → ℕ → ℕ
  /-- A single point admits at most both labels. -/
  base_point : ∀ p, 1 ≤ p → count 1 p ≤ 2
  /-- One parameter yields at most two dichotomies. -/
  base_dim : ∀ N, 1 ≤ N → count N 1 ≤ 2
  /-- Cover's geometric "add one point" recursion. -/
  cover_recursion : ∀ N p, 1 ≤ N → 1 ≤ p →
    count (N + 1) (p + 1) ≤ count N (p + 1) + count N p




/-- Cover's function is itself a dichotomy system, with the recursion holding as
an *equality*. This witnesses non-vacuity and tightness of the bound. -/
def coverCountSystem : DichotomySystem where
  count := coverCount
  base_point _ hp := le_of_eq (coverCount_one_left hp)
  base_dim N _ := le_of_eq (coverCount_one_right N)
  cover_recursion _ p hN _ := le_of_eq (coverCount_recurrence hN p)


end Catalog.Novelty.CoverDichotomy


