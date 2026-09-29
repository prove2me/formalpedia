-- Prove2me | solution 1 for Catalog.Novelty.OrbitalRigidity.numOrbits_pow_lt_of_not_trivial
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:46:54.139675+00:00
-- url     : https://prove2.me/submissions/5453d8c9-3b1d-47ac-95b1-3ac1e00396c5

import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Novelty/OrbitalRigidity.lean ====
/-
# Orbital Rigidity: equality at `k = 2` forces triviality

**Phase A research file (Novelty domain).**

Let `G` be a group acting on a set `X`.  The diagonal action of `G` on `X × X`
partitions `X × X` into *orbitals*.  Each orbital is contained in a product
`orbit G x ×ˢ orbit G y` of two orbits, so the orbital partition always
*refines* the "square of the orbit partition".  The central question of this
file is:

> when is the refinement an equality?

The answer is a sharp rigidity statement: **never**, unless the action is
trivial.  We prove this in three increasingly quantitative forms.

* `orbits_sq_eq_orbitals_iff_trivial` — the set-theoretic form, valid for an
  arbitrary group acting on an arbitrary (possibly infinite, possibly empty)
  set: every orbital equals a product of orbits iff every group element fixes
  every point.

* `rigidity_variance_identity` / `rigidity_quantitative` — the counting form.
  Writing `r` for the number of orbits on `X`, `s` for the number of orbitals,
  `n = |X|` and `F g = |Fix(g)|`, Burnside's lemma turns `r` and `s` into the
  first and second moments of `F` over the uniform measure on `G`.  Hence

  `|G| · (s - r²) = ∑_{g ∈ G} (F g - r)²`,

  i.e. **the rigidity defect is exactly the variance of the fixed-point
  statistic**.  Bounding the sum below by the terms coming from the kernel of
  the action gives the quantitative refinement

  `|K| · (n - r)² ≤ |G| · (s - r²)`,

  where `K` is the set of elements acting trivially.  Since `n > r` exactly
  when the action is nontrivial, this simultaneously proves `s ≥ r²`, the
  equality case, and an explicit lower bound on the defect.  A Cauchy–Schwarz
  correction on the non-kernel part sharpens this to
  `|K| · (n - r)² ≤ (|G| - |K|) · (s - r²)`
  (`rigidity_quantitative_sharp`), and the extremal actions are classified:
  equality holds exactly when every element outside the kernel fixes the same
  number of points (`rigidity_equality_iff_constant_fixity`).

* `numOrbits_pow_eq_iff_trivial` — the higher-arity form.  A Chebyshev/monovary
  argument upgrades the moment inequality to `s_{k+1} ≥ s_k · r`, whence for
  every `k ≥ 2` the number of `G`-orbits on `Xᵏ` is `> rᵏ` unless the action is
  trivial.

The proof mixes three areas: group actions (orbit–stabilizer / Burnside),
probability (the variance of a random variable and its vanishing locus), and
order-theoretic combinatorics (Chebyshev's sum inequality via `Monovary`).

## Lab notes (data computed by Burnside sums over explicit permutation groups)

`n = |X|`, `r = #orbits`, `s = #orbitals`, `K` = kernel, `F` = fixed-point vector.

| action                      | `n` | `|G|` | `F`                     | `r` | `s` | `s - r²` | `|K|(n-r)²` | `(|G|-|K|)(s-r²)` | `|G|(s-r²)` |
|-----------------------------|-----|-------|-------------------------|-----|-----|----------|-------------|-------------------|-------------|
| trivial on 3 points         | 3   | 1     | `[3]`                   | 3   | 9   | 0        | 0           | 0                 | 0           |
| `ℤ/2` swap on 2             | 2   | 2     | `[2,0]`                 | 1   | 2   | 1        | 1           | **1**             | 2           |
| `ℤ/2` swap `(0 1)` on 3     | 3   | 2     | `[3,1]`                 | 2   | 5   | 1        | 1           | **1**             | 2           |
| `ℤ/3` rotation on 3         | 3   | 3     | `[3,0,0]`               | 1   | 3   | 2        | 4           | **4**             | 6           |
| `S₃` on 3                   | 3   | 6     | `[3,1,1,1,0,0]`         | 1   | 2   | 1        | 4           | 5                 | 6           |
| `ℤ/2` `(0 1)(2 3)` on 4     | 4   | 2     | `[4,0]`                 | 2   | 8   | 4        | 4           | **4**             | 8           |
| Klein four regular on 4     | 4   | 4     | `[4,0,0,0]`             | 1   | 4   | 3        | 9           | **9**             | 12          |
| `ℤ/4` regular on 4          | 4   | 4     | `[4,0,0,0]`             | 1   | 4   | 3        | 9           | **9**             | 12          |
| `D₄` on the square          | 4   | 8     | `[4,0,0,0,0,0,2,2]`     | 1   | 3   | 2        | 9           | 14                | 16          |
| `ℤ/5` regular on 5          | 5   | 5     | `[5,0,0,0,0]`           | 1   | 5   | 4        | 16          | **16**            | 20          |
| `ℤ/3` on 5 (`(0 1 2)`)      | 5   | 3     | `[5,2,2]`               | 3   | 11  | 2        | 4           | **4**             | 6           |
| Klein four on 6 points      | 6   | 4     | `[6,2,2,2]`             | 3   | 12  | 3        | 9           | **9**             | 12          |

Readings of the table.

* `s = r²` occurs only in the first row: this is `orbits_sq_eq_orbitals_card_iff_trivial`.
* The bold entries are the cases where `rigidity_quantitative_sharp` is an *equality*; they are
  exactly the rows whose non-identity elements all have the same number of fixed points.  This
  is not a coincidence of the sample: `rigidity_equality_iff_constant_fixity` proves that for a
  nontrivial action, equality holds **iff** the fixity is constant off the kernel.  `S₃`
  (`F = [3,1,1,1,0,0]`) and `D₄` (`F = [4,0,0,0,0,0,2,2]`) have non-constant fixity and are
  strict.  The last row (Klein four generated by `(0 1)(2 3)` and `(2 3)(4 5)`) shows that the
  extremal class is genuinely wider than "same fixed set": the three involutions there fix
  three *different* pairs of points, yet all fix two points, so equality still holds.
* The last column shows that the weaker bound `rigidity_quantitative` is never attained for a
  nontrivial action; the Cauchy–Schwarz correction in Part 7 is what makes the bound sharp.
-/

namespace Catalog.Novelty.OrbitalRigidity

open MulAction Finset

/-! ## Basic definitions -/

-- [dropped: platform already declares numOrbits]
-- [dropped: platform already declares fixCount]
-- [dropped: platform already declares ActsTrivially]
variable {G X : Type*} [Group G] [MulAction G X]

/-! ## Part 1: the set-theoretic rigidity theorem

No finiteness assumptions at all. -/

/-- Every orbital is contained in a product of two orbits: the orbital partition of `X × X`
refines the square of the orbit partition of `X`. -/
theorem orbit_prod_subset (x y : X) :
    orbit G ((x, y) : X × X) ⊆ (orbit G x) ×ˢ (orbit G y) := by
  rintro ⟨a, b⟩ ⟨g, hg⟩
  exact ⟨⟨g, congrArg Prod.fst hg⟩, ⟨g, congrArg Prod.snd hg⟩⟩

/-- **Rigidity at `k = 2`.**  The orbital partition of `X × X` coincides with the square of the
orbit partition of `X` if and only if the action of `G` on `X` is trivial.

This is sharp in both directions and needs no finiteness hypothesis: the forward implication
extracts, from the single membership `(x, g • x) ∈ orbit G x ×ˢ orbit G x`, an element that
simultaneously fixes `x` and moves `x` to `g • x`. -/
theorem orbits_sq_eq_orbitals_iff_trivial :
    (∀ x y : X, orbit G ((x, y) : X × X) = (orbit G x) ×ˢ (orbit G y)) ↔ ActsTrivially G X := by
  constructor
  · intro h g x
    have hmem : ((x, g • x) : X × X) ∈ (orbit G x) ×ˢ (orbit G x) :=
      ⟨mem_orbit_self x, mem_orbit x g⟩
    rw [← h x x] at hmem
    obtain ⟨a, ha⟩ := hmem
    have h1 : a • x = x := congrArg Prod.fst ha
    have h2 : a • x = g • x := congrArg Prod.snd ha
    rw [h1] at h2
    exact h2.symm
  · intro h x y
    refine Set.Subset.antisymm (orbit_prod_subset x y) ?_
    rintro ⟨a, b⟩ ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩
    simp only [h g x, h g' y] at hg hg'
    exact ⟨1, by simp [← hg, ← hg']⟩

/-- A restatement of `orbits_sq_eq_orbitals_iff_trivial` purely in terms of the two orbit
equivalence relations: the orbit relation on pairs is the product of the orbit relations iff
the action is trivial. -/
theorem orbitRel_prod_iff_trivial :
    (∀ x y x' y' : X, ((∃ g : G, g • x = x') ∧ (∃ g : G, g • y = y')) ↔
        (∃ g : G, g • x = x' ∧ g • y = y')) ↔ ActsTrivially G X := by
  rw [← orbits_sq_eq_orbitals_iff_trivial]
  constructor
  · intro h x y
    ext ⟨a, b⟩
    constructor
    · intro hab; exact orbit_prod_subset x y hab
    · rintro ⟨hx, hy⟩
      obtain ⟨g, hg1, hg2⟩ := (h x y a b).1 ⟨hx, hy⟩
      exact ⟨g, Prod.ext hg1 hg2⟩
  · intro h x y x' y'
    constructor
    · rintro ⟨hx, hy⟩
      have : ((x', y') : X × X) ∈ orbit G ((x, y) : X × X) := by
        rw [h x y]; exact ⟨hx, hy⟩
      obtain ⟨g, hg⟩ := this
      exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩
    · rintro ⟨g, hg1, hg2⟩
      exact ⟨⟨g, hg1⟩, ⟨g, hg2⟩⟩

/-! ## Part 2: fixed-point counts of the diagonal actions -/

theorem fixCount_one : fixCount X (1 : G) = Nat.card X := by
  have h : fixedBy X (1 : G) = Set.univ := by ext x; simp
  rw [fixCount, h]
  exact Nat.card_congr (Equiv.Set.univ X)

/-- The fixed points of `g` on `Xᵏ` form the `k`-th power of its fixed-point set on `X`. -/
theorem fixCount_pi (g : G) (k : ℕ) : fixCount (Fin k → X) g = (fixCount X g) ^ k := by
  have e : (fixedBy (Fin k → X) g) ≃ (Fin k → fixedBy X g) := by
    refine Equiv.trans (Equiv.subtypeEquivRight
        (p := fun f : Fin k → X => f ∈ fixedBy (Fin k → X) g)
        (q := fun f : Fin k → X => ∀ i, f i ∈ fixedBy X g) ?_) Equiv.subtypePiEquivPi
    intro f; simp [mem_fixedBy, funext_iff, Pi.smul_apply]
  show Nat.card _ = (Nat.card _) ^ k
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]

/-- The fixed points of `g` on `X × X` form the square of its fixed-point set on `X`. -/
theorem fixCount_prod (g : G) : fixCount (X × X) g = (fixCount X g) ^ 2 := by
  have e : (fixedBy (X × X) g) ≃ (fixedBy X g) × (fixedBy X g) := by
    refine Equiv.trans (Equiv.subtypeEquivRight (p := fun p : X × X => p ∈ fixedBy (X × X) g)
      (q := fun p : X × X => p.1 ∈ fixedBy X g ∧ p.2 ∈ fixedBy X g) ?_) Equiv.subtypeProdEquivProd
    rintro ⟨a, b⟩; simp [mem_fixedBy, Prod.ext_iff]
  show Nat.card _ = (Nat.card _) ^ 2
  rw [Nat.card_congr e, Nat.card_prod, sq]

/-! ## Part 3: Burnside's lemma as a moment computation -/

/-- Burnside's lemma, phrased with `Nat.card`. -/
theorem burnside_natCard [Fintype G] [Finite X] :
    ∑ g : G, fixCount X g = numOrbits G X * Nat.card G := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have : ∀ g : G, Fintype (fixedBy X g) := fun g => Fintype.ofFinite _
  have : Fintype (orbitRel.Quotient G X) := Fintype.ofFinite _
  simp only [fixCount, numOrbits, Nat.card_eq_fintype_card]
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X

/-- The `k`-th moment of the fixed-point statistic counts orbits on `Xᵏ`. -/
theorem burnside_pow [Fintype G] [Finite X] (k : ℕ) :
    ∑ g : G, (fixCount X g) ^ k = numOrbits G (Fin k → X) * Nat.card G := by
  simp only [← fixCount_pi]
  exact burnside_natCard

/-- The second moment of the fixed-point statistic counts orbitals. -/
theorem burnside_prod [Fintype G] [Finite X] :
    ∑ g : G, (fixCount X g) ^ 2 = numOrbits G (X × X) * Nat.card G := by
  simp only [← fixCount_prod]
  exact burnside_natCard

/-- Orbitals and orbits on `X²` are counted by the same number. -/
theorem numOrbits_prod_eq_pi [Fintype G] [Finite X] :
    numOrbits G (X × X) = numOrbits G (Fin 2 → X) := by
  have h := (burnside_prod (G := G) (X := X)).symm.trans (burnside_pow (G := G) (X := X) 2)
  have hN : 0 < Nat.card G := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hN h

/-! ## Part 4: orbits versus points -/

theorem numOrbits_le_card [Finite X] : numOrbits G X ≤ Nat.card X :=
  Nat.card_le_card_of_surjective (Quotient.mk _) Quotient.mk_surjective

theorem numOrbits_eq_card_of_trivial (h : ActsTrivially G X) : numOrbits G X = Nat.card X := by
  refine Nat.card_congr (Equiv.ofBijective (Quotient.mk _) ⟨?_, Quotient.mk_surjective⟩).symm
  intro a b hab
  obtain ⟨g, hg⟩ := Quotient.exact hab
  simpa [h g b] using hg.symm

/-- A nontrivial action has strictly fewer orbits than points. -/
theorem numOrbits_lt_card_of_not_trivial [Finite X] (h : ¬ ActsTrivially G X) :
    numOrbits G X < Nat.card X := by
  rcases lt_or_eq_of_le (numOrbits_le_card (G := G) (X := X)) with h1 | h1
  · exact h1
  · refine absurd (fun g x => ?_) h
    have hb : Function.Bijective (Quotient.mk (orbitRel G X)) := by
      rw [Nat.bijective_iff_surjective_and_card]
      exact ⟨Quotient.mk_surjective, h1.symm⟩
    exact hb.1 (Quotient.sound ⟨g, rfl⟩)

theorem actsTrivially_pi (h : ActsTrivially G X) (k : ℕ) : ActsTrivially G (Fin k → X) :=
  fun g f => funext fun i => h g (f i)

theorem actsTrivially_prod (h : ActsTrivially G X) : ActsTrivially G (X × X) :=
  fun g p => Prod.ext (h g p.1) (h g p.2)

/-! ## Part 5: the variance identity and the quantitative rigidity theorem -/

/-- **The rigidity defect is a variance.**  For a finite group acting on a finite set,

`|G| · (s - r²) = ∑_{g ∈ G} (|Fix g| - r)²`,

where `r` is the number of orbits and `s` the number of orbitals.  Equivalently, `s - r²` is
the variance of the fixed-point statistic under the uniform measure on `G`.  Both sides are
computed by Burnside's lemma applied to `X` and to `X × X`. -/
theorem rigidity_variance_identity [Fintype G] [Finite X] :
    (Nat.card G : ℚ) * ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2)
      = ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2 := by
  have hN : (Nat.card G : ℚ) = (((Finset.univ : Finset G).card : ℕ) : ℚ) := by
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  have e1 : ∑ g : G, ((fixCount X g : ℚ)) = (numOrbits G X : ℚ) * Nat.card G := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (burnside_natCard (G := G) (X := X))
  have e2 : ∑ g : G, ((fixCount X g : ℚ)) ^ 2 = (numOrbits G (X × X) : ℚ) * Nat.card G := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (burnside_prod (G := G) (X := X))
  have expand : ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2
      = (∑ g : G, ((fixCount X g : ℚ)) ^ 2)
        - 2 * (numOrbits G X : ℚ) * (∑ g : G, ((fixCount X g : ℚ)))
        + (((Finset.univ : Finset G).card : ℕ) : ℚ) * (numOrbits G X : ℚ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun g _ => by ring :
      ∀ g ∈ (Finset.univ : Finset G), ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2
        = (fixCount X g : ℚ) ^ 2 - 2 * (numOrbits G X : ℚ) * (fixCount X g : ℚ)
          + (numOrbits G X : ℚ) ^ 2)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp [nsmul_eq_mul]
  rw [expand, e1, e2, ← hN]
  ring

/-- **Quantitative rigidity.**  With `n = |X|`, `r` the number of orbits, `s` the number of
orbitals and `K = {g : g acts trivially}` the kernel of the action,

`|K| · (n - r)² ≤ |G| · (s - r²)`.

Every element of the kernel fixes all of `X`, so contributes exactly `(n - r)²` to the
variance.  For a nontrivial action `n - r ≥ 1`, so the right-hand side is positive. -/
theorem rigidity_quantitative [Fintype G] [Finite X] :
    (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) * ((Nat.card X : ℚ) - (numOrbits G X : ℚ)) ^ 2
      ≤ (Nat.card G : ℚ) * ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2) := by
  classical
  rw [rigidity_variance_identity]
  set r : ℚ := (numOrbits G X : ℚ) with hr
  set T : Finset G := Finset.univ.filter (fun g => ∀ x : X, g • x = x) with hT
  have hcard : (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) = (T.card : ℚ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : T ⊆ (Finset.univ : Finset G) := Finset.filter_subset _ _
  have hkey : ∑ g ∈ T, ((fixCount X g : ℚ) - r) ^ 2
      ≤ ∑ g ∈ (Finset.univ : Finset G), ((fixCount X g : ℚ) - r) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _; positivity
  have hval : ∑ g ∈ T, ((fixCount X g : ℚ) - r) ^ 2
      = (T.card : ℚ) * (((Nat.card X : ℚ)) - r) ^ 2 := by
    rw [Finset.sum_congr rfl (fun g hg => ?_), Finset.sum_const, nsmul_eq_mul]
    have hg' : ∀ x : X, g • x = x := (Finset.mem_filter.1 hg).2
    have : fixCount X g = Nat.card X := by
      have h : fixedBy X g = Set.univ := by ext x; simpa using hg' x
      rw [fixCount, h]
      exact Nat.card_congr (Equiv.Set.univ X)
    rw [this]
  rw [hcard, ← hval]
  exact hkey

/-- The orbital count always dominates the square of the orbit count (Cauchy–Schwarz). -/
theorem orbits_sq_le_orbitals [Fintype G] [Finite X] :
    (numOrbits G X) ^ 2 ≤ numOrbits G (X × X) := by
  have h := rigidity_variance_identity (G := G) (X := X)
  have hpos : (0 : ℚ) ≤ ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  rw [← h] at hpos
  have hN : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos
  have : (0 : ℚ) ≤ (numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2 :=
    nonneg_of_mul_nonneg_right hpos hN
  have : ((numOrbits G X : ℚ)) ^ 2 ≤ (numOrbits G (X × X) : ℚ) := by linarith
  exact_mod_cast this

/-- **Rigidity, counting form.**  The number of orbitals equals the square of the number of
orbits iff the action is trivial. -/
theorem orbits_sq_eq_orbitals_card_iff_trivial [Fintype G] [Finite X] :
    numOrbits G (X × X) = (numOrbits G X) ^ 2 ↔ ActsTrivially G X := by
  constructor
  · intro heq
    by_contra hnt
    have hlt : numOrbits G X < Nat.card X := numOrbits_lt_card_of_not_trivial hnt
    have hq := rigidity_quantitative (G := G) (X := X)
    rw [heq] at hq
    have hzero : (Nat.card G : ℚ) *
        (((numOrbits G X : ℕ) ^ 2 : ℕ) - (numOrbits G X : ℚ) ^ 2) = 0 := by
      push_cast; ring
    rw [hzero] at hq
    have h1 : (1 : ℚ) ≤ ((Nat.card X : ℚ) - (numOrbits G X : ℚ)) := by
      have : (numOrbits G X : ℚ) + 1 ≤ (Nat.card X : ℚ) := by exact_mod_cast hlt
      linarith
    have hK : (1 : ℚ) ≤ (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) := by
      have : 0 < Nat.card {g : G // ∀ x : X, g • x = x} := by
        haveI : Finite {g : G // ∀ x : X, g • x = x} := Subtype.finite
        have : Nonempty {g : G // ∀ x : X, g • x = x} := ⟨⟨1, fun x => one_smul G x⟩⟩
        exact Nat.card_pos
      exact_mod_cast this
    nlinarith [hq, h1, hK]
  · intro h
    rw [numOrbits_eq_card_of_trivial (actsTrivially_prod h), numOrbits_eq_card_of_trivial h,
      Nat.card_prod, sq]

/-! ## Part 6: the higher-arity hierarchy -/

/-- Chebyshev's sum inequality applied to the moments of the fixed-point statistic:
the orbit counts on powers of `X` grow at least geometrically with ratio `r`. -/
theorem numOrbits_mul_le_succ [Fintype G] [Finite X] (k : ℕ) :
    numOrbits G (Fin k → X) * numOrbits G X ≤ numOrbits G (Fin (k + 1) → X) := by
  have hmono : Monovary (fun g : G => fixCount X g ^ k) (fun g : G => fixCount X g) :=
    fun i j hij => Nat.pow_le_pow_left hij.le k
  have hcheb : (∑ g : G, fixCount X g ^ k) * (∑ g : G, fixCount X g)
      ≤ Fintype.card G * ∑ g : G, fixCount X g ^ (k + 1) := by
    simpa [pow_succ] using hmono.sum_mul_sum_le_card_mul_sum
  rw [burnside_pow, burnside_natCard, burnside_pow] at hcheb
  have hNc : Fintype.card G = Nat.card G := (Nat.card_eq_fintype_card).symm
  rw [hNc] at hcheb
  have hN : 0 < Nat.card G := Nat.card_pos
  have h2 : (numOrbits G (Fin k → X) * numOrbits G X) * (Nat.card G * Nat.card G)
      ≤ (numOrbits G (Fin (k + 1) → X)) * (Nat.card G * Nat.card G) := by
    calc (numOrbits G (Fin k → X) * numOrbits G X) * (Nat.card G * Nat.card G)
        = (numOrbits G (Fin k → X) * Nat.card G) * (numOrbits G X * Nat.card G) := by ring
      _ ≤ Nat.card G * (numOrbits G (Fin (k + 1) → X) * Nat.card G) := hcheb
      _ = (numOrbits G (Fin (k + 1) → X)) * (Nat.card G * Nat.card G) := by ring
  exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hN hN)

/-- **Higher-arity rigidity.**  For a nontrivial action and every `k ≥ 2`, the number of
`G`-orbits on `Xᵏ` strictly exceeds `rᵏ`. -/
theorem numOrbits_pow_lt_of_not_trivial [Fintype G] [Finite X] (h : ¬ ActsTrivially G X)
    {k : ℕ} (hk : 2 ≤ k) : (numOrbits G X) ^ k < numOrbits G (Fin k → X) := by
  have hne : Nonempty X := by
    by_contra hemp
    exact h fun g x => absurd ⟨x⟩ hemp
  have hr1 : 1 ≤ numOrbits G X := by
    have : Nonempty (orbitRel.Quotient G X) := ⟨Quotient.mk _ (Classical.arbitrary X)⟩
    exact Nat.card_pos
  -- base case `k = 2`
  have hbase : (numOrbits G X) ^ 2 < numOrbits G (Fin 2 → X) := by
    rw [← numOrbits_prod_eq_pi]
    rcases lt_or_eq_of_le (orbits_sq_le_orbitals (G := G) (X := X)) with hlt | heq
    · exact hlt
    · exact absurd (orbits_sq_eq_orbitals_card_iff_trivial.1 heq.symm) h
  revert hk
  induction k with
  | zero => intro hk; omega
  | succ m ih =>
    intro hk
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · omega
      · simpa using hbase
    · have hprev : (numOrbits G X) ^ m < numOrbits G (Fin m → X) := ih (by omega)
      calc (numOrbits G X) ^ (m + 1) = (numOrbits G X) ^ m * numOrbits G X := by ring
        _ < numOrbits G (Fin m → X) * numOrbits G X := by
            exact Nat.mul_lt_mul_of_lt_of_le hprev le_rfl hr1
        _ ≤ numOrbits G (Fin (m + 1) → X) := numOrbits_mul_le_succ m

/-- **Rigidity at every arity `k ≥ 2`.**  The number of `G`-orbits on `Xᵏ` equals the `k`-th
power of the number of orbits on `X` iff the action is trivial. -/
theorem numOrbits_pow_eq_iff_trivial [Fintype G] [Finite X] {k : ℕ} (hk : 2 ≤ k) :
    numOrbits G (Fin k → X) = (numOrbits G X) ^ k ↔ ActsTrivially G X := by
  constructor
  · intro heq
    by_contra h
    exact absurd heq (numOrbits_pow_lt_of_not_trivial h hk).ne'
  · intro h
    rw [numOrbits_eq_card_of_trivial (actsTrivially_pi h k), numOrbits_eq_card_of_trivial h,
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]


/-! ## Part 7: the sharp quantitative rigidity bound

The bound of `rigidity_quantitative` only uses the contribution of the kernel `K` to the
variance.  Applying Cauchy–Schwarz to the *complementary* part of the group — whose total
deviation is forced, by `∑_{g} (F g - r) = 0`, to equal `-|K|(n - r)` — improves it to

`|K| · (n - r)² ≤ (|G| - |K|) · (s - r²)`,

which is an equality for every action whose non-kernel elements all have the same number of
fixed points (`rigidity_equality_of_constant_fixity`), e.g. the swap action of `ℤ/2` on two
points (`1 · 1 = 1 · 1`) or the rotation action of `ℤ/3` on three points (`1 · 4 = 2 · 2`). -/

section Sharp

variable [Fintype G] [Finite X]

open scoped Classical in
-- [dropped: platform already declares kernelFinset]
open scoped Classical in
omit [Finite X] in
theorem card_kernelFinset :
    (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) = ((kernelFinset G X).card : ℚ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

open scoped Classical in
omit [Finite X] in
theorem fixCount_eq_card_of_mem_kernelFinset {g : G} (hg : g ∈ kernelFinset G X) :
    (fixCount X g : ℚ) = (Nat.card X : ℚ) := by
  have hg' : ∀ x : X, g • x = x := (Finset.mem_filter.1 hg).2
  have h : fixedBy X g = Set.univ := by ext x; simpa using hg' x
  have : fixCount X g = Nat.card X := by
    rw [fixCount, h]; exact Nat.card_congr (Equiv.Set.univ X)
  exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) this

open scoped Classical in
/-- The deviations of the fixed-point statistic from its mean sum to zero. -/
theorem sum_deviation_eq_zero :
    ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) = 0 := by
  have e1 : ∑ g : G, ((fixCount X g : ℚ)) = (numOrbits G X : ℚ) * Nat.card G := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (burnside_natCard (G := G) (X := X))
  have hN : (Nat.card G : ℚ) = (((Finset.univ : Finset G).card : ℕ) : ℚ) := by
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  rw [Finset.sum_sub_distrib, e1, Finset.sum_const, nsmul_eq_mul, ← hN]
  ring

open scoped Classical in
/-- **Sharp quantitative rigidity.**  `|K| · (n - r)² ≤ (|G| - |K|) · (s - r²)`, where `K` is
the kernel of the action.  This strictly improves `rigidity_quantitative` (whose right-hand
side has `|G|` in place of `|G| - |K|`); the improvement comes from Cauchy–Schwarz applied to
the non-kernel part of `G`, whose total deviation from the mean is forced to be `-|K|(n-r)`. -/
theorem rigidity_quantitative_sharp :
    (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) * ((Nat.card X : ℚ) - (numOrbits G X : ℚ)) ^ 2
      ≤ ((Nat.card G : ℚ) - (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ)) *
          ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2) := by
  classical
  set r : ℚ := (numOrbits G X : ℚ) with hr
  set D : ℚ := (Nat.card X : ℚ) - r with hD
  set T : Finset G := kernelFinset G X with hT
  set A : ℚ := (T.card : ℚ) with hA
  set B : ℚ := ((Tᶜ : Finset G).card : ℚ) with hB
  set E : ℚ := (numOrbits G (X × X) : ℚ) - r ^ 2 with hE
  set S : ℚ := ∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r) ^ 2 with hS
  have hcard : (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) = A := card_kernelFinset
  have hAB : A + B = (Nat.card G : ℚ) := by
    rw [hA, hB, ← Nat.cast_add, Finset.card_add_card_compl, Nat.card_eq_fintype_card]
  have hTsum : ∑ g ∈ T, ((fixCount X g : ℚ) - r) = A * D := by
    rw [Finset.sum_congr rfl (fun g hg => by
      rw [fixCount_eq_card_of_mem_kernelFinset (X := X) hg]), Finset.sum_const, nsmul_eq_mul]
  have hTsq : ∑ g ∈ T, ((fixCount X g : ℚ) - r) ^ 2 = A * D ^ 2 := by
    rw [Finset.sum_congr rfl (fun g hg => by
      rw [fixCount_eq_card_of_mem_kernelFinset (X := X) hg]), Finset.sum_const, nsmul_eq_mul]
  have hTcsum : ∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r) = -(A * D) := by
    have h := Finset.sum_add_sum_compl T (fun g : G => (fixCount X g : ℚ) - r)
    rw [hTsum, sum_deviation_eq_zero] at h
    linarith
  have hCS : (A * D) ^ 2 ≤ B * S := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Tᶜ : Finset G))
      (f := fun g : G => (fixCount X g : ℚ) - r)
    rw [hTcsum] at h
    simpa [hS, hB, neg_sq] using h
  have hNE : (Nat.card G : ℚ) * E = A * D ^ 2 + S := by
    rw [hE, hr, rigidity_variance_identity]
    rw [← Finset.sum_add_sum_compl T (fun g : G => ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2)]
    rw [hTsq]
  have hN : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos
  have hAnn : (0 : ℚ) ≤ A := by positivity
  have hBnn : (0 : ℚ) ≤ B := by positivity
  have hgoal : A * D ^ 2 ≤ B * E := by
    nlinarith [hCS, hNE, hAB, hN, hAnn, hBnn, sq_nonneg D, mul_nonneg hAnn (sq_nonneg D),
      mul_nonneg hBnn (sq_nonneg D)]
  rw [hcard]
  have hBv : B = (Nat.card G : ℚ) - A := by linarith
  rw [← hBv]
  exact hgoal

open scoped Classical in
/-- **The sharp bound is attained.**  If every element outside the kernel fixes the same number
`c` of points — as happens for regular actions, sharply transitive actions and Frobenius groups
— then `|K| · (n - r)² = (|G| - |K|) · (s - r²)`. -/
theorem rigidity_equality_of_constant_fixity (c : ℕ)
    (hc : ∀ g : G, (¬ ∀ x : X, g • x = x) → fixCount X g = c) :
    (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) * ((Nat.card X : ℚ) - (numOrbits G X : ℚ)) ^ 2
      = ((Nat.card G : ℚ) - (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ)) *
          ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2) := by
  classical
  set r : ℚ := (numOrbits G X : ℚ) with hr
  set D : ℚ := (Nat.card X : ℚ) - r with hD
  set T : Finset G := kernelFinset G X with hT
  set A : ℚ := (T.card : ℚ) with hA
  set B : ℚ := ((Tᶜ : Finset G).card : ℚ) with hB
  set E : ℚ := (numOrbits G (X × X) : ℚ) - r ^ 2 with hE
  have hcard : (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) = A := card_kernelFinset
  have hAB : A + B = (Nat.card G : ℚ) := by
    rw [hA, hB, ← Nat.cast_add, Finset.card_add_card_compl, Nat.card_eq_fintype_card]
  have hmemc : ∀ g ∈ (Tᶜ : Finset G), (fixCount X g : ℚ) = (c : ℚ) := by
    intro g hg
    have : ¬ ∀ x : X, g • x = x := by
      simpa [hT, kernelFinset, Finset.mem_compl, Finset.mem_filter] using hg
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (hc g this)
  have hTsum : ∑ g ∈ T, ((fixCount X g : ℚ) - r) = A * D := by
    rw [Finset.sum_congr rfl (fun g hg => by
      rw [fixCount_eq_card_of_mem_kernelFinset (X := X) hg]), Finset.sum_const, nsmul_eq_mul]
  have hTsq : ∑ g ∈ T, ((fixCount X g : ℚ) - r) ^ 2 = A * D ^ 2 := by
    rw [Finset.sum_congr rfl (fun g hg => by
      rw [fixCount_eq_card_of_mem_kernelFinset (X := X) hg]), Finset.sum_const, nsmul_eq_mul]
  have hTcsum : ∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r) = -(A * D) := by
    have h := Finset.sum_add_sum_compl T (fun g : G => (fixCount X g : ℚ) - r)
    rw [hTsum, sum_deviation_eq_zero] at h
    linarith
  have hTcsum' : ∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r) = B * ((c : ℚ) - r) := by
    rw [Finset.sum_congr rfl (fun g hg => by rw [hmemc g hg]), Finset.sum_const, nsmul_eq_mul]
  have hTcsq : ∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r) ^ 2 = B * ((c : ℚ) - r) ^ 2 := by
    rw [Finset.sum_congr rfl (fun g hg => by rw [hmemc g hg]), Finset.sum_const, nsmul_eq_mul]
  have hNE : (Nat.card G : ℚ) * E = A * D ^ 2 + B * ((c : ℚ) - r) ^ 2 := by
    rw [hE, hr, rigidity_variance_identity]
    rw [← Finset.sum_add_sum_compl T (fun g : G => ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2)]
    rw [hTsq, hTcsq]
  have hlin : B * ((c : ℚ) - r) = -(A * D) := by rw [← hTcsum', hTcsum]
  rw [hcard]
  have hBv : (Nat.card G : ℚ) - A = B := by linarith
  rw [hBv]
  rcases eq_or_lt_of_le (show (0:ℚ) ≤ B by positivity) with hB0 | hBpos
  · -- the kernel is everything: the action is trivial and both sides vanish
    have hAeq : A = (Nat.card G : ℚ) := by linarith
    have hAD : A * D = 0 := by rw [← neg_eq_zero, ← hlin, ← hB0]; ring
    have hN : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos
    have hD0 : D = 0 := by
      rcases mul_eq_zero.1 hAD with h | h
      · exact absurd (hAeq ▸ h) (ne_of_gt hN)
      · exact h
    rw [hD0, ← hB0]; ring
  · have hN : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos
    have hc' : ((c : ℚ) - r) = -(A * D) / B := by field_simp at hlin ⊢; linarith
    rw [hc'] at hNE
    field_simp at hNE
    have hz : (Nat.card G : ℚ) * (B * E - A * D ^ 2) = 0 := by
      linear_combination hNE + A * D ^ 2 * hAB
    have := mul_eq_zero.1 hz
    rcases this with h | h
    · exact absurd h (ne_of_gt hN)
    · linarith

open scoped Classical in
omit [Finite X] in
/-- Membership in the complement of the kernel finset. -/
theorem mem_compl_kernelFinset_iff {g : G} :
    g ∈ (kernelFinset G X)ᶜ ↔ ¬ ∀ x : X, g • x = x := by
  simp [kernelFinset, Finset.mem_filter]

open scoped Classical in
/-- **Classification of the extremal actions.**  For a nontrivial action, the sharp bound
`|K| · (n - r)² ≤ (|G| - |K|) · (s - r²)` is an equality *precisely* when all elements outside
the kernel fix the same number of points.  This is the equality case of the Cauchy–Schwarz
step, transported through the variance identity. -/
theorem rigidity_equality_iff_constant_fixity (hnt : ¬ ActsTrivially G X) :
    ((Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) * ((Nat.card X : ℚ) - (numOrbits G X : ℚ)) ^ 2
        = ((Nat.card G : ℚ) - (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ)) *
            ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2))
      ↔ ∃ c : ℕ, ∀ g : G, (¬ ∀ x : X, g • x = x) → fixCount X g = c := by
  classical
  constructor
  · intro heq
    set r : ℚ := (numOrbits G X : ℚ) with hr
    set D : ℚ := (Nat.card X : ℚ) - r with hD
    set T : Finset G := kernelFinset G X with hT
    set A : ℚ := (T.card : ℚ) with hA
    set B : ℚ := ((Tᶜ : Finset G).card : ℚ) with hB
    set E : ℚ := (numOrbits G (X × X) : ℚ) - r ^ 2 with hE
    set S : ℚ := ∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r) ^ 2 with hS
    have hcard : (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) = A := card_kernelFinset
    have hAB : A + B = (Nat.card G : ℚ) := by
      rw [hA, hB, ← Nat.cast_add, Finset.card_add_card_compl, Nat.card_eq_fintype_card]
    -- the complement of the kernel is nonempty
    obtain ⟨g₀, hg₀⟩ : ∃ g : G, g ∈ (Tᶜ : Finset G) := by
      by_contra hcon
      push_neg at hcon
      exact hnt fun g x => by
        have := hcon g
        rw [hT, mem_compl_kernelFinset_iff] at this
        exact not_not.1 this x
    have hBpos : (0 : ℚ) < B := by
      have h : 0 < (Tᶜ : Finset G).card := Finset.card_pos.2 ⟨g₀, hg₀⟩
      rw [hB]
      exact_mod_cast h
    have hTsq : ∑ g ∈ T, ((fixCount X g : ℚ) - r) ^ 2 = A * D ^ 2 := by
      rw [Finset.sum_congr rfl (fun g hg => by
        rw [fixCount_eq_card_of_mem_kernelFinset (X := X) hg]), Finset.sum_const, nsmul_eq_mul]
    have hTsum : ∑ g ∈ T, ((fixCount X g : ℚ) - r) = A * D := by
      rw [Finset.sum_congr rfl (fun g hg => by
        rw [fixCount_eq_card_of_mem_kernelFinset (X := X) hg]), Finset.sum_const, nsmul_eq_mul]
    have hTcsum : ∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r) = -(A * D) := by
      have h := Finset.sum_add_sum_compl T (fun g : G => (fixCount X g : ℚ) - r)
      rw [hTsum, sum_deviation_eq_zero] at h
      linarith
    have hNE : (Nat.card G : ℚ) * E = A * D ^ 2 + S := by
      rw [hE, hr, rigidity_variance_identity]
      rw [← Finset.sum_add_sum_compl T
        (fun g : G => ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2)]
      rw [hTsq]
    have hEq : A * D ^ 2 = B * E := by
      rw [hcard] at heq
      have hBv : (Nat.card G : ℚ) - A = B := by linarith
      rw [hBv] at heq
      exact heq
    have hBS : B * S = (A * D) ^ 2 := by
      linear_combination (-B) * hNE + (-(Nat.card G : ℚ)) * hEq + (-(A * D ^ 2)) * hAB
    -- the deviations are constant on the complement of the kernel
    set m : ℚ := -(A * D) / B with hm
    have hexp : ∑ g ∈ Tᶜ, (((fixCount X g : ℚ) - r) - m) ^ 2
        = S - 2 * m * (∑ g ∈ Tᶜ, ((fixCount X g : ℚ) - r)) + B * m ^ 2 := by
      rw [Finset.sum_congr rfl (fun g _ => by ring :
        ∀ g ∈ (Tᶜ : Finset G), (((fixCount X g : ℚ) - r) - m) ^ 2
          = ((fixCount X g : ℚ) - r) ^ 2 - 2 * m * ((fixCount X g : ℚ) - r) + m ^ 2)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
        nsmul_eq_mul, ← hS, ← hB]
    have hzero : ∑ g ∈ Tᶜ, (((fixCount X g : ℚ) - r) - m) ^ 2 = 0 := by
      rw [hexp, hTcsum, hm]
      field_simp
      linarith [hBS]
    have hconst : ∀ g ∈ (Tᶜ : Finset G), ((fixCount X g : ℚ) - r) = m := by
      intro g hg
      have hnn : ∀ g ∈ (Tᶜ : Finset G), (0 : ℚ) ≤ (((fixCount X g : ℚ) - r) - m) ^ 2 :=
        fun g _ => sq_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero g hg
      have h2 : ((fixCount X g : ℚ) - r) - m = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    refine ⟨fixCount X g₀, fun g hg => ?_⟩
    have hgc : g ∈ (Tᶜ : Finset G) := by rw [hT, mem_compl_kernelFinset_iff]; exact hg
    have h1 := hconst g hgc
    have h2 := hconst g₀ hg₀
    have : (fixCount X g : ℚ) = (fixCount X g₀ : ℚ) := by linarith
    exact_mod_cast this
  · rintro ⟨c, hc⟩
    exact rigidity_equality_of_constant_fixity c hc

end Sharp

/-! ## Part 8: the structural mechanism — an independence criterion for two `G`-sets

Rigidity at `k = 2` is the diagonal case of a general *independence* phenomenon.  For two
`G`-sets `X` and `Y`, the orbits of `G` on `X × Y` are exactly the products `orbit x × orbit y`
precisely when, for every `x`, the point stabiliser `G_x` is still transitive on each `G`-orbit
in `Y`.  Specialising `Y = X` kills the action: `G_x` fixes `x`, so transitivity of `G_x` on
`orbit G x` forces `orbit G x = {x}`. -/

section TwoSets

variable {Y : Type*} [MulAction G Y]

/-- **Independence criterion.**  Orbits on `X × Y` are products of orbits iff every point
stabiliser `G_x` acts transitively on every `G`-orbit of `Y`. -/
theorem orbital_prod_eq_iff_stabilizer_transitive :
    (∀ (x : X) (y : Y), orbit G ((x, y) : X × Y) = (orbit G x) ×ˢ (orbit G y)) ↔
      (∀ (x : X) (y : Y), orbit (stabilizer G x) y = orbit G y) := by
  constructor
  · intro h x y
    refine Set.Subset.antisymm (fun b hb => ?_) (fun b hb => ?_)
    · obtain ⟨k, hk⟩ := hb
      exact ⟨(k : G), hk⟩
    · obtain ⟨g, hg⟩ := hb
      have hmem : ((x, b) : X × Y) ∈ (orbit G x) ×ˢ (orbit G y) := ⟨mem_orbit_self x, ⟨g, hg⟩⟩
      rw [← h x y] at hmem
      obtain ⟨a, ha⟩ := hmem
      exact ⟨⟨a, congrArg Prod.fst ha⟩, congrArg Prod.snd ha⟩
  · intro h x y
    refine Set.Subset.antisymm ?_ ?_
    · rintro ⟨a, b⟩ ⟨g, hg⟩
      exact ⟨⟨g, congrArg Prod.fst hg⟩, ⟨g, congrArg Prod.snd hg⟩⟩
    · rintro ⟨a, b⟩ ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩
      have hx : g • x = a := hg
      have hy : g' • y = b := hg'
      have hb : g⁻¹ • b ∈ orbit G y :=
        ⟨g⁻¹ * g', show (g⁻¹ * g') • y = g⁻¹ • b by rw [mul_smul, hy]⟩
      rw [← h x y] at hb
      obtain ⟨k, hk⟩ := hb
      have hk' : (k : G) • y = g⁻¹ • b := hk
      have hkx : (k : G) • x = x := k.2
      refine ⟨g * (k : G), ?_⟩
      show ((g * (k : G)) • x, (g * (k : G)) • y) = (a, b)
      rw [mul_smul, mul_smul, hkx, hk', hx, smul_inv_smul]

end TwoSets

/-- **Self-independence forces triviality.**  A `G`-set cannot be independent of itself unless
the action is trivial: `G_x` is transitive on every orbit of `X` iff `G` acts trivially.
Together with `orbital_prod_eq_iff_stabilizer_transitive` (taken with `Y = X`) this gives a
second, purely structural proof of `orbits_sq_eq_orbitals_iff_trivial`. -/
theorem stabilizer_transitive_self_iff_trivial :
    (∀ (x y : X), orbit (stabilizer G x) y = orbit G y) ↔ ActsTrivially G X := by
  constructor
  · intro h g x
    have hx : orbit G x ⊆ {x} := by
      rw [← h x x]
      rintro b ⟨k, hk⟩
      have : (k : G) • x = b := hk
      rw [← this, k.2]
      exact rfl
    exact (hx (mem_orbit x g) : g • x = x)
  · intro h x y
    ext b
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(k : G), hk⟩
    · rintro ⟨g, hg⟩
      have : g • y = b := hg
      refine ⟨1, ?_⟩
      show ((1 : stabilizer G x) : G) • y = b
      rw [h ((1 : stabilizer G x) : G) y, ← this, h g y]

end Catalog.Novelty.OrbitalRigidity
section
open Catalog.Novelty.OrbitalRigidity
open MulAction Finset
variable {G X : Type*} [Group G] [MulAction G X]

theorem solution [Fintype G] [Finite X] (h : ¬ ActsTrivially G X)
    {k : ℕ} (hk : 2 ≤ k) :
    (numOrbits G X) ^ k < numOrbits G (Fin k → X) := by
  first
  | exact Catalog.Novelty.OrbitalRigidity.numOrbits_pow_lt_of_not_trivial h hk
  | exact Catalog.Novelty.OrbitalRigidity.numOrbits_pow_lt_of_not_trivial
  | exact @Catalog.Novelty.OrbitalRigidity.numOrbits_pow_lt_of_not_trivial _ _ h k hk
  | apply Catalog.Novelty.OrbitalRigidity.numOrbits_pow_lt_of_not_trivial
  | exact Catalog.Novelty.OrbitalRigidity.numOrbits_pow_lt_of_not_trivial ..


end
