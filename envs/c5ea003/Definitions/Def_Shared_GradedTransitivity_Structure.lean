-- Prove2me | Definitions.Def_Shared_GradedTransitivity_Structure
-- name    : Shared_GradedTransitivity_Structure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:53:32.475264+00:00
-- url     : https://prove2.me/theorems/665d3ff9-ba55-4209-94e1-e6558002627f
-- title:
--   Aether Catalog definitions — Shared_GradedTransitivity_Structure
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GradedTransitivity.Structure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GradedTransitivity/Structure.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_GSet

/-!
# The ring of series with poles only at `q = 1`, and the residue at `q = 1`

Two structural refinements of the main theorem.

1. **Algebra.** The power series admitting a denominator `(1-q)^k` form a
   subring `ratOneSubring` of `ℚ[[q]]` (it is the image of the localisation
   `ℚ[X]_{(1-X)}`).  Hilbert series of eventually `r`-transitive graded
   `G`-sets live in it, hence sums and Cauchy products of such Hilbert series
   are again rational with a pole only at `q = 1`.

2. **Residue.** For an eventually `r`-transitive graded `G`-set the pole at
   `q = 1` is *simple with residue `-1`*: if `(1-q)·H(q) = P(q)` then
   `P(1) = 1`.  This is a genuinely quantitative statement — it says the
   numerator of the Hilbert series always evaluates to the eventual number of
   orbits, which is `1` exactly because of transitivity.

## Main results

* `ratOneSubring` and `gen_hilbertSeq_mem_ratOneSubring`.
* `eval_one_numerator_of_eventually_const`, `hilbertSeq_residue_one`.
-/

namespace GradedTransitivity

open Polynomial

/-! ### The subring of series with denominator a power of `1-q` -/

/-- The set of power series `f` such that `(1-X)^k f` is a polynomial for some
`k`; equivalently the rational functions whose only pole is at `q = 1`. -/
noncomputable def ratOneSubring : Subring (PowerSeries ℚ) where
  carrier := {f | ∃ (k : ℕ) (P : ℚ[X]), (1 - PowerSeries.X) ^ k * f = (P : PowerSeries ℚ)}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro f g ⟨k, P, hP⟩ ⟨l, Q, hQ⟩
    refine ⟨k + l, (1 - X) ^ l * P + (1 - X) ^ k * Q, ?_⟩
    have : (1 - PowerSeries.X) ^ (k + l) * (f + g)
        = (1 - PowerSeries.X) ^ l * ((1 - PowerSeries.X) ^ k * f)
          + (1 - PowerSeries.X) ^ k * ((1 - PowerSeries.X) ^ l * g) := by ring
    rw [this, hP, hQ]
    push_cast
    ring
  mul_mem' := by
    rintro f g ⟨k, P, hP⟩ ⟨l, Q, hQ⟩
    refine ⟨k + l, P * Q, ?_⟩
    have : (1 - PowerSeries.X) ^ (k + l) * (f * g)
        = ((1 - PowerSeries.X) ^ k * f) * ((1 - PowerSeries.X) ^ l * g) := by ring
    rw [this, hP, hQ]
    push_cast
    ring
  neg_mem' := by
    rintro f ⟨k, P, hP⟩
    exact ⟨k, -P, by rw [mul_neg, hP]; push_cast; ring⟩




section GradedMembership

variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]



end GradedMembership

/-! ### The residue at `q = 1` -/




section Residue

variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]


end Residue

end GradedTransitivity


