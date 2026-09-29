-- Prove2me | solution 1 for MomentHierarchy.orbitCount_regular_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:30:48.197162+00:00
-- url     : https://prove2.me/submissions/c78a0e5b-d095-4245-a8a4-de93e69f57d0

-- Sol generated from Logic/MomentHierarchy.lean
import Mathlib
import Definitions.Def_Logic_MomentHierarchy
import Theorems.Thm_MomentHierarchy_card_group_mul_orbitCount

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

omit [Fintype G] in
/-- The identity fixes everything: `|X^1| = |X|`. -/
theorem card_fixedBy_one (X : Type*) [MulAction G X] :
    Nat.card (fixedBy X (1 : G)) = Nat.card X := by
  simp [fixedBy]

omit [Fintype G] in
/-- For the left regular action, a nonidentity element has no fixed points. -/
theorem card_fixedBy_regular_ne {g : G} (hg : g ≠ 1) : Nat.card (fixedBy G g) = 0 := by
  have : IsEmpty (fixedBy G g) := by
    constructor
    rintro ⟨x, hx⟩
    rw [mem_fixedBy] at hx
    exact hg (by
      have := congrArg (fun y => y * x⁻¹) hx
      simpa [mul_assoc] using this)
  simp [Nat.card_of_isEmpty]

/-- **Orbit counts of the regular action.** The diagonal left-translation action of `G`
on `G^k` has exactly `|G|^{k-1}` orbits for `k ≥ 1`: the moment collapses to the single
identity term `|G|^k`. -/
theorem orbitCount_regular (k : ℕ) (hk : 1 ≤ k) :
    orbitCount G G k * Nat.card G = Nat.card G ^ k := by
  rw [card_group_mul_orbitCount, Finset.sum_eq_single (1 : G)]
  · rw [card_fixedBy_one (G := G) G]
  · intro b _ hb
    rw [card_fixedBy_regular_ne hb, zero_pow (by omega : k ≠ 0)]
  · intro h
    exact absurd (Finset.mem_univ (1 : G)) h




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
theorem solution(k : ℕ) (hk : 1 ≤ k) :
    orbitCount G G k = Nat.card G ^ (k - 1) := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h := orbitCount_regular (G := G) k hk
  have hk' : Nat.card G ^ k = Nat.card G ^ (k - 1) * Nat.card G := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hk'] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h
