-- Prove2me | solution 1 for RecipeBarycenter.aggregate_ratio_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:45:58.223265+00:00
-- url     : https://prove2.me/submissions/c8eea28b-55bf-48d1-8a30-63f7877dcbb2

-- Sol generated from Novelty/RecipeBarycenterBridge.lean
import Mathlib
import Definitions.Def_Novelty_RecipeBarycenterBridge
import Theorems.Thm_RecipeBarycenter_ratio_eq_one_iff

/-!
# Recipe complexity as convex geometry

A finite menu is modeled by cooking and verification times.  If every dish has
positive verification time, the cooking/verification ratio of the entire menu is
not an arbitrary quotient: it is the barycenter of the individual ratios, weighted
by each dish's share of the total verification work.

This connects the culinary complexity metaphor to convex geometry.  The bridge has
real content: the weights are nonnegative and sum to one, so an aggregate menu
cannot have a ratio outside the range of its dishes.  Moreover, if every dish is
at least break-even (`V ≤ C`), equality at the boundary is rigid: an aggregate
ratio of one forces every individual ratio to be one.

No claim about actual complexity classes, Navier--Stokes, or soufflé hardness is
made: those would require a computational model and reductions not supplied by
timing data alone.
-/

open RecipeBarycenter





/-
Positive individual verification times imply positive total verification time
when the menu is nonempty.
-/
lemma aggregate_verify_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (R : ι → Recipe) (hpos : ∀ i, 0 < (R i).verify) :
    0 < (aggregate R).verify := by
  exact Finset.sum_pos ( fun i _ => hpos i ) Finset.univ_nonempty

/-
Verification shares are nonnegative.
-/

/-
The verification shares form a partition of unity.
-/
theorem sum_weight_eq_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (R : ι → Recipe) (hpos : ∀ i, 0 < (R i).verify) :
    ∑ i, weight R i = 1 := by
  unfold weight;
  rw [ ← Finset.sum_div _ _ _, div_eq_iff ] <;> norm_cast;
  · simp +decide [ aggregate ];
  · exact ne_of_gt ( aggregate_verify_pos R hpos )

/-
**Recipe--barycenter bridge.**  The aggregate ratio is the convex combination
of individual ratios weighted by verification work.
-/
theorem aggregate_ratio_eq_barycenter {ι : Type*} [Fintype ι] [Nonempty ι]
    (R : ι → Recipe) (hpos : ∀ i, 0 < (R i).verify) :
    ratio (aggregate R) = ∑ i, weight R i * ratio (R i) := by
  -- By definition of ratio and weight, we can rewrite the right-hand side.
  unfold ratio weight;
  simp +decide [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, aggregate]
  simp +decide [ne_of_gt (hpos _)]
  rw [ Finset.sum_mul _ _ _ ]

/-
The barycenter cannot exceed a common upper bound for all dish ratios.
-/

/-
The barycenter cannot fall below a common lower bound for all dish ratios.
-/

/-
Hence the aggregate ratio lies in every interval containing all individual
ratios: a direct convex-hull statement in one dimension.
-/

/-
A positive-time recipe has ratio one exactly when cooking and verification
costs agree.
-/

/-
**Boundary rigidity.**  If every dish is physical (`V ≤ C`) and every
verification time is positive, then a globally break-even menu is possible exactly
when every dish is individually break-even.  Convex-geometrically, a barycenter of
points in `[1,∞)` equals the boundary point `1` iff every positively weighted point
is `1`.
-/

/-- A concrete three-dish example illustrating the barycentric identity. -/
example :
    ratio (aggregate ![Recipe.mk 6 2, Recipe.mk 12 3, Recipe.mk 5 5]) =
      (2 / 10 : ℚ) * 3 + (3 / 10 : ℚ) * 4 + (5 / 10 : ℚ) * 1 := by
  norm_num [ratio, aggregate, Fin.sum_univ_succ]


open RecipeBarycenter in
theorem solution{ι : Type*} [Fintype ι] [Nonempty ι]
    (R : ι → Recipe) (hpos : ∀ i, 0 < (R i).verify)
    (hphysical : ∀ i, (R i).verify ≤ (R i).cook) :
    ratio (aggregate R) = 1 ↔ ∀ i, ratio (R i) = 1 := by
  constructor <;> intro h;
  · -- By definition of aggregate, we have that the total cooking time equals the total verification time.
    have h_total : ∑ i, (R i).cook = ∑ i, (R i).verify := by
      exact_mod_cast eq_of_div_eq_one h;
    -- By definition of aggregate, we have that each individual cooking time equals its verification time.
    have h_each : ∀ i, (R i).cook = (R i).verify := by
      exact fun i => le_antisymm ( le_of_not_gt fun hi => by have := Finset.sum_lt_sum ( fun a _ => hphysical a ) ⟨ i, Finset.mem_univ i, hi ⟩ ; aesop ) ( hphysical i );
    exact fun i => ratio_eq_one_iff ( hpos i ) |>.2 ( h_each i );
  · convert aggregate_ratio_eq_barycenter R hpos;
    simp +decide [ h, sum_weight_eq_one R hpos ]
