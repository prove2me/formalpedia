-- Prove2me | Theorems.Thm_MomentHierarchy_orbits_prod_eq_orbits_add_orbits_offDiag
-- name    : MomentHierarchy.orbits_prod_eq_orbits_add_orbits_offDiag
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:36:42.595284+00:00
-- url     : https://prove2.me/theorems/03a77967-58bc-403a-b39c-7ef86fd8dc56
-- title:
--   Rank splitting.
-- statement:
--   **Rank splitting.** The number of orbits on ordered pairs is the number of orbits on
--   points plus the number of orbits on ordered pairs of *distinct* points:
--   `rank = #(X/G) + #(offDiag/G)`.
--
--   ```lean
--   theorem MomentHierarchy.orbits_prod_eq_orbits_add_orbits_offDiag:
--       Nat.card (orbitRel.Quotient G (X × X))
--         = Nat.card (orbitRel.Quotient G X)
--           + Nat.card (orbitRel.Quotient G (offDiagSub G X)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/MomentHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/MomentHierarchy.lean#L407

-- Thm stub generated from Logic/MomentHierarchy.lean
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

theorem MomentHierarchy.orbits_prod_eq_orbits_add_orbits_offDiag:
    Nat.card (orbitRel.Quotient G (X × X))
      = Nat.card (orbitRel.Quotient G X)
        + Nat.card (orbitRel.Quotient G (offDiagSub G X)) := by sorry
