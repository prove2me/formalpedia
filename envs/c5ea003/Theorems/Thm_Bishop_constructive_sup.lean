-- Prove2me | Theorems.Thm_Bishop_constructive_sup
-- name    : Bishop.constructive_sup
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:18:18.925021+00:00
-- url     : https://prove2.me/theorems/42dee435-c8d0-4cf8-b07d-13134c1a19fe
-- title:
--   Bishop's constructive least upper bound principle.
-- statement:
--   **Bishop's constructive least upper bound principle.**
--
--   A set of reals that is nonempty, bounded above, and *located* (in the explicit sense
--   of `LocatedData`) has a least upper bound, and this supremum is enclosed by the
--   explicitly computed rationals of the trisection search, with the exact geometric
--   rate `(2/3)^n (b₀ - a₀)`.
--
--   ```lean
--   theorem Bishop.constructive_sup{S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
--       (h₀ : Enclosing S (a₀, b₀)) :
--       ∃ u : ℝ, IsLUB S u ∧ ∀ n : ℕ,
--         ((bisect D.L a₀ b₀ n).1 : ℝ) ≤ u ∧ u ≤ ((bisect D.L a₀ b₀ n).2 : ℝ) ∧
--           ((bisect D.L a₀ b₀ n).2 : ℝ) - ((bisect D.L a₀ b₀ n).1 : ℝ)
--             = (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveSup.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveSup.lean#L121

-- Thm stub generated from Logic/ConstructiveAnalysis/ConstructiveSup.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveSup
/-
# Bishop's constructive least upper bound principle

Classically every nonempty set of reals that is bounded above has a supremum.  That
proof is not constructive: it decides, for a rational `q`, whether `q` is an upper
bound of the set, which is in general undecidable.  Bishop's replacement assumes
that the set is **located**: it comes equipped with a *decision procedure* `L` such
that for rationals `p < q`, `L p q = true` guarantees that `q` is an upper bound,
and `L p q = false` produces a member of the set above `p`.  (Both alternatives may
hold; only their disjunction is asserted, which is what makes the datum obtainable
in practice.)

From such a datum the supremum is computed by an explicit **trisection search**
(`Bishop.bisect`), producing at every stage a pair of rationals `p n ≤ sup ≤ q n`
whose width is exactly `(2/3)^n (b₀ - a₀)`:

* `Bishop.bisect_width` : the exact geometric rate;
* `Bishop.bisect_invariant` : the enclosure invariant, proved by induction;
* `Bishop.constructive_sup` : the supremum exists, is the least upper bound, and is
  enclosed by the explicitly computed rationals with the stated rate;
* `Bishop.constructive_sup_reg` : the supremum, presented as a Bishop real, i.e. as a
  regular sequence of rationals with the canonical modulus `1/(n+1)`.

The located hypothesis is exactly what the classical proof hides: `Bishop.
locatedData_of_decidable` shows that assuming the classically valid but
constructively unavailable decision "is `q` an upper bound?" one recovers a located
datum, so the principle is classically equivalent to the ordinary completeness
axiom.
-/


open Bishop

open Set

theorem Bishop.constructive_sup{S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) :
    ∃ u : ℝ, IsLUB S u ∧ ∀ n : ℕ,
      ((bisect D.L a₀ b₀ n).1 : ℝ) ≤ u ∧ u ≤ ((bisect D.L a₀ b₀ n).2 : ℝ) ∧
        ((bisect D.L a₀ b₀ n).2 : ℝ) - ((bisect D.L a₀ b₀ n).1 : ℝ)
          = (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) := by sorry
