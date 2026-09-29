-- Prove2me | Theorems.Thm_Bishop_enclosing_bisectStep
-- name    : Bishop.enclosing_bisectStep
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:17:52.274583+00:00
-- url     : https://prove2.me/theorems/1610462a-3f0a-4629-b80f-7bdc375df16c
-- title:
--   Enclosing bisectStep
-- statement:
--   Formal statement of `Bishop.enclosing_bisectStep` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bishop.enclosing_bisectStep{S : Set ℝ} (D : LocatedData S) {pq : ℚ × ℚ}
--       (hlt : pq.1 < pq.2) (h : Enclosing S pq) : Enclosing S (bisectStep D.L pq) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveSup.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveSup.lean#L96

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

theorem Bishop.enclosing_bisectStep{S : Set ℝ} (D : LocatedData S) {pq : ℚ × ℚ}
    (hlt : pq.1 < pq.2) (h : Enclosing S pq) : Enclosing S (bisectStep D.L pq) := by sorry
