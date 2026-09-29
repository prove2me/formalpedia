-- Prove2me | Theorems.Thm_Catalog_Novelty_OrbitalRigidity_orbitRel_prod_iff_trivial
-- name    : Catalog.Novelty.OrbitalRigidity.orbitRel_prod_iff_trivial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:13:42.11599+00:00
-- url     : https://prove2.me/theorems/35d9c5f8-bcc7-4a2d-8844-78a174f765bf
-- title:
--   A restatement of `orbits_sq_eq_orbitals_iff_trivial` purely in terms of the two orbit
-- statement:
--   A restatement of `orbits_sq_eq_orbitals_iff_trivial` purely in terms of the two orbit
--   equivalence relations: the orbit relation on pairs is the product of the orbit relations iff
--   the action is trivial.
--
--   ```lean
--   theorem Catalog.Novelty.OrbitalRigidity.orbitRel_prod_iff_trivial:
--       (∀ x y x' y' : X, ((∃ g : G, g • x = x') ∧ (∃ g : G, g • y = y')) ↔
--           (∃ g : G, g • x = x' ∧ g • y = y')) ↔ ActsTrivially G X := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/OrbitalRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/OrbitalRigidity.lean#L141

-- Thm stub generated from Novelty/OrbitalRigidity.lean
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

theorem Catalog.Novelty.OrbitalRigidity.orbitRel_prod_iff_trivial:
    (∀ x y x' y' : X, ((∃ g : G, g • x = x') ∧ (∃ g : G, g • y = y')) ↔
        (∃ g : G, g • x = x' ∧ g • y = y')) ↔ ActsTrivially G X := by sorry
