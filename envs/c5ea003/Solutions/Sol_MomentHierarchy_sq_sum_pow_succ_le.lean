-- Prove2me | solution 1 for MomentHierarchy.sq_sum_pow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:28:03.645711+00:00
-- url     : https://prove2.me/submissions/09a8cc36-10e7-4d57-924b-b64a59436dff

-- Sol generated from Logic/MomentHierarchy.lean
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

/-!
# The Burnside Moment Hierarchy

For a finite group `G` acting on a finite type `X`, write

  `a g := |X^g| = Nat.card (MulAction.fixedBy X g)`

for the number of points fixed by `g`, and

  `S k := ∑ g : G, a g ^ k`,   `o k := #((Fin k → X) / G)`

for the `k`-th *moment* of the fixed-point statistic and the number of orbits of the
diagonal action of `G` on `k`-tuples of points of `X`.

The organising result of this file is the **moment identity**

  `S k = o k * |G|`   (`sum_fixedPoints_pow_eq_orbits_mul_card`)

valid for *every* `k`. Its instances are classical:

* `k = 0` : the single orbit on the one-point set of `0`-tuples (`orbitCount_zero`);
* `k = 1` : **Burnside's lemma** / the Cauchy–Frobenius orbit-counting theorem
  (`moment_one`);
* `k = 2` : the number of orbits on ordered pairs, i.e. the **rank** of the
  permutation action (`moment_two`).

Beyond the identity itself we develop the *hierarchy*: the sequence `k ↦ o k` inherits
strong structural properties from the fact that it is (up to the factor `|G|`) a moment
sequence of a nonnegative integer random variable:

* `orbits_pow_le_succ` : `o` is nondecreasing from `k = 1` on;
* `orbits_pow_log_convex` : `o (k+1) ^ 2 ≤ o k * o (k+2)`, i.e. the orbit-counting
  sequence is **log-convex** (a Cauchy–Schwarz / AM–GM phenomenon);
* `card_pow_le_card_group_mul_orbits` and `orbits_pow_le_card_pow` : the sandwich
  `|X| ^ k ≤ |G| * o k ≤ |G| * |X| ^ k`;
* `card_group_dvd_moment` : `|G|` divides every moment `S k`.

A bilinear refinement `sum_fixedPoints_mul_eq_orbits_prod_mul_card` computes
`∑ g, |X^g| * |Y^g|` as `|G|` times the number of orbits on `X × Y`; this is the
orbit-counting form of the inner product of two permutation characters.

All statements are phrased with `Nat.card`, so no decidability assumptions are needed.
-/

open MulAction Finset

open MomentHierarchy


variable {G X Y ι : Type*} [Group G] [MulAction G X] [MulAction G Y]









variable {G X Y : Type*} [Group G] [Fintype G] [MulAction G X] [MulAction G Y]






variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X]






/-- Pointwise AM–GM in `ℕ`: `2 x^{k+1} y^{k+1} ≤ x^k y^{k+2} + y^k x^{k+2}`. -/
theorem two_mul_pow_succ_le (x y k : ℕ) :
    2 * (x ^ (k + 1) * y ^ (k + 1)) ≤ x ^ k * y ^ (k + 2) + y ^ k * x ^ (k + 2) := by
  have h : 2 * x * y ≤ x ^ 2 + y ^ 2 := two_mul_le_add_sq x y
  calc 2 * (x ^ (k + 1) * y ^ (k + 1)) = (x ^ k * y ^ k) * (2 * x * y) := by ring
    _ ≤ (x ^ k * y ^ k) * (x ^ 2 + y ^ 2) := Nat.mul_le_mul_left _ h
    _ = x ^ k * y ^ (k + 2) + y ^ k * x ^ (k + 2) := by ring




variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X]













/-! ## Cycle 2: the rank layer, off-diagonal splitting and 2-transitivity

The second moment `∑ g, |X^g|^2` is the *rank* of the permutation action. We refine the
identity by splitting the `G`-set `X × X` into its diagonal (a copy of `X`) and its
off-diagonal part, obtaining `rank = #(X/G) + #(offDiag/G)`. This is the `k = 2` case of
the Stirling/Bell transform relating moments of the fixed-point statistic to orbit counts
on *distinct* tuples, and it yields a clean spectral criterion:
the action is transitive and 2-transitive **iff** the second moment equals `2 |G|`.
-/



variable {G X : Type*} [Group G] [MulAction G X]







variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X]






variable {G : Type*} [Group G] [Fintype G]







/-! ## Cycle 3: mixed moments, Cauchy–Schwarz geometry and superexponential growth

The moment identity is the diagonal case of a *mixed moment* identity valid for an
arbitrary finite family of `G`-sets: `∑ g ∏ i |X_i^g| = |G| · #((∏ i X_i)/G)`. Reading
`g ↦ |X^g|` as the permutation character of `X`, the mixed identity says that orbit
counts on products compute inner products of permutation characters. Cauchy–Schwarz for
this inner product then becomes a purely combinatorial statement about orbit counts, and
the log-convexity of the moment hierarchy upgrades to superexponential growth
`#(X/G)^k ≤ #((X^k)/G)`.
-/


variable {G : Type*} [Group G] [Fintype G]







variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nonempty X]






/-! ## Cycle 6: suborbits — the second moment of a transitive action

For a transitive action the second level of the hierarchy is a *local* invariant: the
orbits of `G` on `X × X` are in bijection with the orbits of a single point stabiliser
`H = Stab(x₀)` on `X` (the **suborbits**). The bijection sends the `H`-orbit of `y` to the
`G`-orbit of the pair `(x₀, y)`. Combined with the moment identity this evaluates the
second moment of a transitive action purely in terms of `H`. -/


variable {G X : Type*} [Group G] [MulAction G X]


variable [Fintype G] [Finite X]





open MomentHierarchy in
theorem solution{ι : Type*} (s : Finset ι) (a : ι → ℕ) (k : ℕ) :
    (∑ i ∈ s, a i ^ (k + 1)) ^ 2 ≤ (∑ i ∈ s, a i ^ k) * (∑ i ∈ s, a i ^ (k + 2)) := by
  have expand : (∑ i ∈ s, a i ^ (k + 1)) ^ 2
      = ∑ i ∈ s, ∑ j ∈ s, a i ^ (k + 1) * a j ^ (k + 1) := by
    rw [sq, Finset.sum_mul_sum]
  have expandR : (∑ i ∈ s, a i ^ k) * (∑ i ∈ s, a i ^ (k + 2))
      = ∑ i ∈ s, ∑ j ∈ s, a i ^ k * a j ^ (k + 2) := by
    rw [Finset.sum_mul_sum]
  have swap : ∑ i ∈ s, ∑ j ∈ s, a i ^ k * a j ^ (k + 2)
      = ∑ i ∈ s, ∑ j ∈ s, a j ^ k * a i ^ (k + 2) := Finset.sum_comm
  have key : 2 * (∑ i ∈ s, ∑ j ∈ s, a i ^ (k + 1) * a j ^ (k + 1))
      ≤ 2 * (∑ i ∈ s, ∑ j ∈ s, a i ^ k * a j ^ (k + 2)) := by
    have h2 : 2 * (∑ i ∈ s, ∑ j ∈ s, a i ^ k * a j ^ (k + 2))
        = ∑ i ∈ s, ∑ j ∈ s, (a i ^ k * a j ^ (k + 2) + a j ^ k * a i ^ (k + 2)) := by
      simp only [Finset.sum_add_distrib, two_mul]
      rw [← swap]
    rw [h2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => two_mul_pow_succ_le (a i) (a j) k
  rw [expand, expandR]
  omega
