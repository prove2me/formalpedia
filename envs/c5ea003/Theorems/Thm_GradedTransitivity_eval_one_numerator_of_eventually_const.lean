-- Prove2me | Theorems.Thm_GradedTransitivity_eval_one_numerator_of_eventually_const
-- name    : GradedTransitivity.eval_one_numerator_of_eventually_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:17.404375+00:00
-- url     : https://prove2.me/theorems/63f4f1a9-9f93-43d3-b67a-ad756a46ee25
-- title:
--   Residue theorem.
-- statement:
--   **Residue theorem.**  If `a` is eventually equal to `c` and
--   `(1-q)Â·â a n qâ¿ = P(q)`, then `P(1) = c`: the pole of the generating function
--   at `q = 1` is simple with residue `-c`.
--
--   ```lean
--   theorem GradedTransitivity.eval_one_numerator_of_eventually_const{a : ℕ → ℚ} {c : ℚ} {N : ℕ} {P : ℚ[X]}
--       (hev : ∀ n ≥ N, a n = c) (h : (1 - PowerSeries.X) * gen a = (P : PowerSeries ℚ)) :
--       P.eval 1 = c := by sorry
--
--   variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Structure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Structure.lean#L127

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

theorem GradedTransitivity.eval_one_numerator_of_eventually_const{a : ℕ → ℚ} {c : ℚ} {N : ℕ} {P : ℚ[X]}
    (hev : ∀ n ≥ N, a n = c) (h : (1 - PowerSeries.X) * gen a = (P : PowerSeries ℚ)) :
    P.eval 1 = c := by sorry
