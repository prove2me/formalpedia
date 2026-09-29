-- Prove2me | solution 1 for MomentHierarchy.card_ne_pairs_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:26:39.012406+00:00
-- url     : https://prove2.me/submissions/76a4cc8f-a1d0-45e8-97a8-c1fcb46fd2da

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
theorem solution(F : Type*) [Finite F] :
    Nat.card {q : F × F // q.1 ≠ q.2} + Nat.card F = Nat.card F ^ 2 := by
  classical
  have hdiag : Nat.card {q : F × F // q.1 = q.2} = Nat.card F :=
    Nat.card_congr
      { toFun := fun q => q.1.1
        invFun := fun x => ⟨(x, x), rfl⟩
        left_inv := fun q => Subtype.ext (Prod.ext rfl q.2)
        right_inv := fun _ => rfl }
  have h := Nat.card_congr (Equiv.sumCompl (fun q : F × F => q.1 = q.2))
  rw [Nat.card_sum, Nat.card_prod, hdiag] at h
  simp only [ne_eq, sq]
  omega
