-- Prove2me | Theorems.Thm_MomentHierarchy_orbitCount_log_convex
-- name    : MomentHierarchy.orbitCount_log_convex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:37:46.790767+00:00
-- url     : https://prove2.me/theorems/a82556da-2dcd-408f-8ea3-ce0a4358dfec
-- title:
--   Log-convexity of the orbit hierarchy.
-- statement:
--   **Log-convexity of the orbit hierarchy.** The sequence `k ↦ #((X^k)/G)` is
--   log-convex: `o(k+1)^2 ≤ o(k) · o(k+2)`. Equivalently the moments of the fixed-point
--   statistic satisfy the Cauchy–Schwarz inequality, and the factor `|G|^2` cancels.
--
--   ```lean
--   theorem MomentHierarchy.orbitCount_log_convex(k : ℕ) :
--       orbitCount G X (k + 1) ^ 2 ≤ orbitCount G X k * orbitCount G X (k + 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/MomentHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/MomentHierarchy.lean#L280

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

theorem MomentHierarchy.orbitCount_log_convex(k : ℕ) :
    orbitCount G X (k + 1) ^ 2 ≤ orbitCount G X k * orbitCount G X (k + 2) := by sorry
