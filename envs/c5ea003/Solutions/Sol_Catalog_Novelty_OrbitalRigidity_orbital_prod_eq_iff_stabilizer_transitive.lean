-- Prove2me | solution 1 for Catalog.Novelty.OrbitalRigidity.orbital_prod_eq_iff_stabilizer_transitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:46:22.003287+00:00
-- url     : https://prove2.me/submissions/33bee4cd-5e5d-4cc2-9097-15dabd3683c2

-- Sol generated from Novelty/OrbitalRigidity.lean
import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity
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










/-! ## Part 8: the structural mechanism — an independence criterion for two `G`-sets

Rigidity at `k = 2` is the diagonal case of a general *independence* phenomenon.  For two
`G`-sets `X` and `Y`, the orbits of `G` on `X × Y` are exactly the products `orbit x × orbit y`
precisely when, for every `x`, the point stabiliser `G_x` is still transitive on each `G`-orbit
in `Y`.  Specialising `Y = X` kills the action: `G_x` fixes `x`, so transitivity of `G_x` on
`orbit G x` forces `orbit G x = {x}`. -/


variable {Y : Type*} [MulAction G Y]





open Catalog.Novelty.OrbitalRigidity in
theorem solution:
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
