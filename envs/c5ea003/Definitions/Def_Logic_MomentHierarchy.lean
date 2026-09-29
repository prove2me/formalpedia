-- Prove2me | Definitions.Def_Logic_MomentHierarchy
-- name    : Logic_MomentHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:31.889108+00:00
-- url     : https://prove2.me/theorems/e078acba-d288-4632-b4d8-21d70f44a27b
-- title:
--   Aether Catalog definitions — Logic_MomentHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.MomentHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/MomentHierarchy.lean by skeleton subtraction
import Mathlib

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

namespace MomentHierarchy

section FixedPoints

variable {G X Y ι : Type*} [Group G] [MulAction G X] [MulAction G Y]

/-- A function `f : ι → X` is fixed by `g` for the pointwise action iff each value is. -/
theorem mem_fixedBy_pi (g : G) (f : ι → X) :
    f ∈ fixedBy (ι → X) g ↔ ∀ i, f i ∈ fixedBy X g := by
  simp [mem_fixedBy, funext_iff]

/-- The fixed points of `g` on the function space `ι → X` are exactly the functions
into the fixed points of `g` on `X`. -/
def fixedByPiEquiv (g : G) : (fixedBy (ι → X) g) ≃ (ι → fixedBy X g) where
  toFun f i := ⟨f.1 i, (mem_fixedBy_pi g f.1).1 f.2 i⟩
  invFun F := ⟨fun i => (F i).1, (mem_fixedBy_pi g _).2 fun i => (F i).2⟩
  left_inv f := by ext i; rfl
  right_inv F := by ext i; rfl


/-- A pair is fixed by `g` iff both coordinates are. -/
theorem mem_fixedBy_prod (g : G) (p : X × Y) :
    p ∈ fixedBy (X × Y) g ↔ p.1 ∈ fixedBy X g ∧ p.2 ∈ fixedBy Y g := by
  cases p; simp [mem_fixedBy, Prod.ext_iff]

/-- The fixed points of `g` on a product action are the product of the fixed points. -/
def fixedByProdEquiv (g : G) : (fixedBy (X × Y) g) ≃ (fixedBy X g) × (fixedBy Y g) where
  toFun p := (⟨p.1.1, ((mem_fixedBy_prod g p.1).1 p.2).1⟩,
              ⟨p.1.2, ((mem_fixedBy_prod g p.1).1 p.2).2⟩)
  invFun q := ⟨(q.1.1, q.2.1), (mem_fixedBy_prod g _).2 ⟨q.1.2, q.2.2⟩⟩
  left_inv p := by ext <;> rfl
  right_inv q := by ext <;> rfl


end FixedPoints

section Burnside

variable {G X Y : Type*} [Group G] [Fintype G] [MulAction G X] [MulAction G Y]




end Burnside

section Instances

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X]




end Instances

section Inequalities



end Inequalities

section Hierarchy

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X]

/-- Abbreviation: `orbitCount G X k` is the number of orbits of `G` on `k`-tuples of
points of `X`. -/
noncomputable def orbitCount (G X : Type*) [Group G] [MulAction G X] (k : ℕ) : ℕ :=
  Nat.card (orbitRel.Quotient G (Fin k → X))










end Hierarchy


/-! ## Cycle 2: the rank layer, off-diagonal splitting and 2-transitivity

The second moment `∑ g, |X^g|^2` is the *rank* of the permutation action. We refine the
identity by splitting the `G`-set `X × X` into its diagonal (a copy of `X`) and its
off-diagonal part, obtaining `rank = #(X/G) + #(offDiag/G)`. This is the `k = 2` case of
the Stirling/Bell transform relating moments of the fixed-point statistic to orbit counts
on *distinct* tuples, and it yields a clean spectral criterion:
the action is transitive and 2-transitive **iff** the second moment equals `2 |G|`.
-/

section OffDiag

/-- The off-diagonal `{(x, y) : x ≠ y}` as a `G`-invariant sub-action of `X × X`. -/
def offDiagSub (G X : Type*) [Group G] [MulAction G X] : SubMulAction G (X × X) where
  carrier := {p : X × X | p.1 ≠ p.2}
  smul_mem' g p hp := by
    simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd] at hp ⊢
    exact fun h => hp (smul_left_cancel g h)

variable {G X : Type*} [Group G] [MulAction G X]


theorem mem_fixedBy_offDiag (g : G) (p : offDiagSub G X) :
    p ∈ fixedBy (offDiagSub G X) g ↔
      (p : X × X).1 ∈ fixedBy X g ∧ (p : X × X).2 ∈ fixedBy X g := by
  simp [mem_fixedBy, Subtype.ext_iff, Prod.ext_iff]

/-- The `g`-fixed off-diagonal pairs are the ordered pairs of distinct `g`-fixed points. -/
def fixedByOffDiagEquiv (g : G) :
    fixedBy (offDiagSub G X) g ≃ {q : (fixedBy X g) × (fixedBy X g) // q.1 ≠ q.2} where
  toFun p := ⟨(⟨(p.1 : X × X).1, ((mem_fixedBy_offDiag g p.1).1 p.2).1⟩,
               ⟨(p.1 : X × X).2, ((mem_fixedBy_offDiag g p.1).1 p.2).2⟩),
    fun h => p.1.2 (congrArg Subtype.val h)⟩
  invFun q := ⟨⟨((q.1.1 : X), (q.1.2 : X)), fun h => q.2 (Subtype.ext h)⟩, by
    rw [mem_fixedBy_offDiag]
    exact ⟨q.1.1.2, q.1.2.2⟩⟩
  left_inv p := by ext <;> rfl
  right_inv q := by ext <;> rfl


end OffDiag

section Rank

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X]




end Rank

section Regular

variable {G : Type*} [Group G] [Fintype G]





end Regular


/-! ## Cycle 3: mixed moments, Cauchy–Schwarz geometry and superexponential growth

The moment identity is the diagonal case of a *mixed moment* identity valid for an
arbitrary finite family of `G`-sets: `∑ g ∏ i |X_i^g| = |G| · #((∏ i X_i)/G)`. Reading
`g ↦ |X^g|` as the permutation character of `X`, the mixed identity says that orbit
counts on products compute inner products of permutation characters. Cauchy–Schwarz for
this inner product then becomes a purely combinatorial statement about orbit counts, and
the log-convexity of the moment hierarchy upgrades to superexponential growth
`#(X/G)^k ≤ #((X^k)/G)`.
-/

section MixedMoments

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
theorem mem_fixedBy_pi_family {ι : Type*} (X : ι → Type*) [∀ i, MulAction G (X i)] (g : G)
    (f : ∀ i, X i) : f ∈ fixedBy (∀ i, X i) g ↔ ∀ i, f i ∈ fixedBy (X i) g := by
  simp [mem_fixedBy, funext_iff]

/-- Fixed points of a product of `G`-sets are products of fixed points. -/
def fixedByPiFamilyEquiv {ι : Type*} (X : ι → Type*) [∀ i, MulAction G (X i)] (g : G) :
    fixedBy (∀ i, X i) g ≃ (∀ i, fixedBy (X i) g) where
  toFun f i := ⟨f.1 i, (mem_fixedBy_pi_family X g f.1).1 f.2 i⟩
  invFun F := ⟨fun i => (F i).1, (mem_fixedBy_pi_family X g _).2 fun i => (F i).2⟩
  left_inv f := by ext i; rfl
  right_inv F := by ext i; rfl



end MixedMoments

section Growth

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nonempty X]




end Growth


/-! ## Cycle 6: suborbits — the second moment of a transitive action

For a transitive action the second level of the hierarchy is a *local* invariant: the
orbits of `G` on `X × X` are in bijection with the orbits of a single point stabiliser
`H = Stab(x₀)` on `X` (the **suborbits**). The bijection sends the `H`-orbit of `y` to the
`G`-orbit of the pair `(x₀, y)`. Combined with the moment identity this evaluates the
second moment of a transitive action purely in terms of `H`. -/

section Suborbits

variable {G X : Type*} [Group G] [MulAction G X]


variable [Fintype G] [Finite X]



end Suborbits

end MomentHierarchy


