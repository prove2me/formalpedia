-- Prove2me | Theorems.Thm_GradedTransitivity_hilbertSeq_residue_one
-- name    : GradedTransitivity.hilbertSeq_residue_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:29.891107+00:00
-- url     : https://prove2.me/theorems/84b4160f-31ac-40bb-bfa7-10e6766a66a1
-- title:
--   For an eventually `r`-transitive graded `G`-set the numerator of the
-- statement:
--   For an eventually `r`-transitive graded `G`-set the numerator of the
--   Hilbert series always satisfies `P(1) = 1`: the pole at `q = 1` is simple with
--   residue `-1`, reflecting the single orbit in high grades.
--
--   ```lean
--   theorem GradedTransitivity.hilbertSeq_residue_one(r N : ℕ) (h : ∀ n ≥ N, IsRTransitive (G n) (Y n) r)
--       {P : ℚ[X]} (hP : (1 - PowerSeries.X) * gen (hilbertSeq G Y r) = (P : PowerSeries ℚ)) :
--       P.eval 1 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Structure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Structure.lean#L155

-- Thm stub generated from Shared/GradedTransitivity/Structure.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Definitions.Def_Shared_GradedTransitivity_Structure

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

open GradedTransitivity

open Polynomial

/-! ### The subring of series with denominator a power of `1-q` -/






variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]




/-! ### The residue at `q = 1` -/





variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]

theorem GradedTransitivity.hilbertSeq_residue_one(r N : ℕ) (h : ∀ n ≥ N, IsRTransitive (G n) (Y n) r)
    {P : ℚ[X]} (hP : (1 - PowerSeries.X) * gen (hilbertSeq G Y r) = (P : PowerSeries ℚ)) :
    P.eval 1 = 1 := by sorry
