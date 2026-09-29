-- Prove2me | solution 1 for Catalog.Novelty.OrbitalRigidity.rigidity_quantitative_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T10:40:13.072235+00:00
-- url     : https://prove2.me/submissions/1c3708e0-7625-4698-a5b4-32f0d377398f

-- Sol generated from Novelty/OrbitalRigidity.lean
import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity
import Theorems.Thm_Catalog_Novelty_OrbitalRigidity_rigidity_variance_identity
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

open Catalog.Novelty.OrbitalRigidity

open MulAction Finset

/-! ## Basic definitions -/




variable {G X : Type*} [Group G] [MulAction G X]

/-! ## Part 1: the set-theoretic rigidity theorem

No finiteness assumptions at all. -/




/-! ## Part 2: fixed-point counts of the diagonal actions -/




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




/-! ## Part 4: orbits versus points -/






/-! ## Part 5: the variance identity and the quantitative rigidity theorem -/





/-! ## Part 6: the higher-arity hierarchy -/





/-! ## Part 7: the sharp quantitative rigidity bound

The bound of `rigidity_quantitative` only uses the contribution of the kernel `K` to the
variance.  Applying Cauchy–Schwarz to the *complementary* part of the group — whose total
deviation is forced, by `∑_{g} (F g - r) = 0`, to equal `-|K|(n - r)` — improves it to

`|K| · (n - r)² ≤ (|G| - |K|) · (s - r²)`,

which is an equality for every action whose non-kernel elements all have the same number of
fixed points (`rigidity_equality_of_constant_fixity`), e.g. the swap action of `ℤ/2` on two
points (`1 · 1 = 1 · 1`) or the rotation action of `ℤ/3` on three points (`1 · 4 = 2 · 2`). -/


variable [Fintype G] [Finite X]


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






/-! ## Part 8: the structural mechanism — an independence criterion for two `G`-sets

Rigidity at `k = 2` is the diagonal case of a general *independence* phenomenon.  For two
`G`-sets `X` and `Y`, the orbits of `G` on `X × Y` are exactly the products `orbit x × orbit y`
precisely when, for every `x`, the point stabiliser `G_x` is still transitive on each `G`-orbit
in `Y`.  Specialising `Y = X` kills the action: `G_x` fixes `x`, so transitivity of `G_x` on
`orbit G x` forces `orbit G x = {x}`. -/


variable {Y : Type*} [MulAction G Y]





open Catalog.Novelty.OrbitalRigidity in
open scoped Classical in
theorem solution:
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
