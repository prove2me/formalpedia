-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.parentSeed_isSeed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:03:00.295293+00:00
-- url     : https://prove2.me/submissions/9512829f-595a-489d-b61b-545549a1e1d9

-- Sol generated from Geometry/HyperbolicBerggrenTreeDepth.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth

/-!
# Hyperbolic–Pythagorean Geodesics, cycle VIII: the tree structure of the depth function

Cycles I–VII studied a *single* Berggren node `(m,n)` and the effect of one Berggren move
on its hyperbolic position.  The quantity that the mission statement is really about — the
**path length**, i.e. the combinatorial depth `k` at which a node occurs — was so far only
touched in the negative (`depth_not_bounded_by_distance`: depth is not bounded by a constant
multiple of the hyperbolic distance).  This file settles the positive half and the
book-keeping that makes "the depth" a well-defined function in the first place.

## Main results

* `Reaches p k` : the inductive predicate "`p` is obtained from the root seed `(2,1)` by `k`
  Berggren moves".
* `reaches_isSeed` : every reachable pair is a Euclid seed (soundness).
* `seed_reaches` : **completeness of the Berggren tree.** *Every* Euclid seed is reachable.
  The proof runs the explicit inverse move `parentSeed`, which is a genuine trichotomy in
  the slope: `n/m ∈ (1/2, 1)`, `(1/3, 1/2)`, `(0, 1/3)` selects `B₁`, `B₂`, `B₃`.
* `reaches_unique` : **the Berggren tree really is a tree.**  A seed is reachable at exactly
  one depth, so `depth` is a well-defined function on seeds.
* `reaches_fst_le` : a node at depth `k` has `m ≤ 2·3^k`; hence
  `reaches_log_hyp_le` : `log c ≤ log 8 + k · log 9`, and
  `dist_le_depth` / `depth_ge_dist` : `2 d(i, z) ≤ log 32 + k · log 9`, i.e.
  **the hyperbolic distance is, up to constants, a lower bound for the depth**.
  Combined with `depth_not_bounded_by_distance` of cycle I this is the exact truth:
  `d ≲ k`, and no reverse inequality holds.
* `mspine_dist_ge` : along the middle (Pell) spine the reverse inequality *does* hold,
  `k · log 2 ≤ d`, so on that branch depth and distance are commensurable.
* `berggren_depth_logarithmic_reach` : **the `O(log N)` statement of the mission, in the
  only form in which it is true.**  For every `N` there is a Berggren node of hypotenuse
  `≥ N` at depth `k = ⌊log₂ N⌋`, and `k · log 2 ≤ log N`.

Together: reaching size `N` costs depth `Θ(log N)` at best (`berggren_depth_logarithmic_reach`
for the upper bound, `depth_ge_dist` for the matching lower bound), while an arbitrary node of
hypotenuse `N` can sit at depth as large as `Θ(√N)` (cycle I).
-/

open HyperbolicBerggrenGeodesics

open Real

/-! ## Part A. Reachability in the Berggren tree -/




/-! ## Part B. The inverse move, and completeness of the tree -/





/-- A Euclid seed with `m = 2n` is the root. -/
theorem seed_two_mul_eq {m n : ℕ} (h : IsSeed m n) (hmn : m = 2 * n) : m = 2 ∧ n = 1 := by
  have : n ∣ Nat.gcd m n := Nat.dvd_gcd ⟨2, by omega⟩ dvd_rfl
  rw [h.cop] at this
  have hn : n = 1 := Nat.dvd_one.mp this
  exact ⟨by omega, hn⟩

/-- A Euclid seed never satisfies `m = 3n`: parity forbids it. -/
theorem seed_three_mul_ne {m n : ℕ} (h : IsSeed m n) : m ≠ 3 * n := by
  intro hmn
  have hd : n ∣ Nat.gcd m n := Nat.dvd_gcd ⟨3, by omega⟩ dvd_rfl
  rw [h.cop] at hd
  have hn : n = 1 := Nat.dvd_one.mp hd
  have := h.parity
  omega





/-! ## Part C. Uniqueness of the depth -/




/-! ## Part D. Depth versus size: the lower bound -/






/-! ## Part E. Depth versus size: the matching upper bound along the Pell spine -/








/-! ## Part F. Depth is not governed by the continued fraction of the slope

The natural guess (conjecture **G1** of `FUTURE_DIRECTIONS.md`) is that a Berggren path is
the additive continued-fraction expansion of the slope `n/m`, so that the depth should equal
the sum of the partial quotients up to a bounded error, or at least up to a fixed
proportionality constant.  This is **false**, and the reason is structural: the move `B₃`
adds `2` to `m/n`, so a long run of `B₃`'s costs only *half* a partial quotient per step,
while the move `B₁` accumulates at the parabolic fixed point `n/m = 1` and costs a *whole*
partial quotient per step.  The two pure spines therefore realise two different
proportionality constants, and no single law can hold. -/










/-! ## Part G. Non-vacuity witnesses -/





open HyperbolicBerggrenGeodesics in
theorem solution{m n : ℕ} (h : IsSeed m n) (hroot : ¬ (m = 2 ∧ n = 1)) :
    IsSeed (parentSeed (m, n)).1 (parentSeed (m, n)).2 := by
  have hpos := h.pos
  have hlt := h.lt
  have hpar := h.parity
  have hne2 : m ≠ 2 * n := fun hc => hroot (seed_two_mul_eq h hc)
  have hne3 : m ≠ 3 * n := seed_three_mul_ne h
  by_cases hA : 2 * n < m
  · by_cases hB : 3 * n < m
    · -- came from `B₃`: parent `(m - 2n, n)`
      simp only [parentSeed, if_pos hA, if_pos hB]
      refine ⟨hpos, by omega, ?_, by omega⟩
      have hd : Nat.gcd (m - 2 * n) n ∣ m := by
        have h1 : Nat.gcd (m - 2 * n) n ∣ (m - 2 * n) + 2 * n :=
          Nat.dvd_add (Nat.gcd_dvd_left _ _) (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2)
        simpa [Nat.sub_add_cancel (by omega : 2 * n ≤ m)] using h1
      have : Nat.gcd (m - 2 * n) n ∣ Nat.gcd m n :=
        Nat.dvd_gcd hd (Nat.gcd_dvd_right _ _)
      rw [h.cop] at this
      exact Nat.dvd_one.mp this
    · -- came from `B₂`: parent `(n, m - 2n)`
      simp only [parentSeed, if_pos hA, if_neg hB]
      refine ⟨by omega, by omega, ?_, by omega⟩
      have hd : Nat.gcd n (m - 2 * n) ∣ m := by
        have h1 : Nat.gcd n (m - 2 * n) ∣ (m - 2 * n) + 2 * n :=
          Nat.dvd_add (Nat.gcd_dvd_right _ _) (Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2)
        simpa [Nat.sub_add_cancel (by omega : 2 * n ≤ m)] using h1
      have : Nat.gcd n (m - 2 * n) ∣ Nat.gcd m n :=
        Nat.dvd_gcd hd (Nat.gcd_dvd_left _ _)
      rw [h.cop] at this
      exact Nat.dvd_one.mp this
  · -- came from `B₁`: parent `(n, 2n - m)`
    simp only [parentSeed, if_neg hA]
    refine ⟨by omega, by omega, ?_, by omega⟩
    have hd : Nat.gcd n (2 * n - m) ∣ m := by
      have h1 : Nat.gcd n (2 * n - m) ∣ 2 * n - (2 * n - m) :=
        Nat.dvd_sub (Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2) (Nat.gcd_dvd_right _ _)
      simpa [Nat.sub_sub_self (by omega : m ≤ 2 * n)] using h1
    have : Nat.gcd n (2 * n - m) ∣ Nat.gcd m n :=
      Nat.dvd_gcd hd (Nat.gcd_dvd_left _ _)
    rw [h.cop] at this
    exact Nat.dvd_one.mp this
