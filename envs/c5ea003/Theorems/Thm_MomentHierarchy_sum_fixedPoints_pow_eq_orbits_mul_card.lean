-- Prove2me | Theorems.Thm_MomentHierarchy_sum_fixedPoints_pow_eq_orbits_mul_card
-- name    : MomentHierarchy.sum_fixedPoints_pow_eq_orbits_mul_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:35:42.730863+00:00
-- url     : https://prove2.me/theorems/34c897b0-8c09-429c-913e-772e0ee90a80
-- title:
--   The moment identity.
-- statement:
--   **The moment identity.** For every `k`, the `k`-th moment of the fixed-point
--   statistic equals `|G|` times the number of orbits of `G` on `k`-tuples:
--   `∑_{g ∈ G} |X^g|^k = #((X^k)/G) · |G|`.
--
--   `k = 1` is Burnside's lemma; `k = 2` computes the rank of the permutation action.
--
--   ```lean
--   theorem MomentHierarchy.sum_fixedPoints_pow_eq_orbits_mul_card[Finite X] (k : ℕ) :
--       ∑ g : G, Nat.card (fixedBy X g) ^ k
--         = Nat.card (orbitRel.Quotient G (Fin k → X)) * Nat.card G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/MomentHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/MomentHierarchy.lean#L105

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

theorem MomentHierarchy.sum_fixedPoints_pow_eq_orbits_mul_card[Finite X] (k : ℕ) :
    ∑ g : G, Nat.card (fixedBy X g) ^ k
      = Nat.card (orbitRel.Quotient G (Fin k → X)) * Nat.card G := by sorry
