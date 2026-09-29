-- Prove2me | solution 1 for GradedTransitivity.hilbertSeq_residue_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:51:02.274891+00:00
-- url     : https://prove2.me/submissions/0d26739a-a97f-4bc1-9a34-edfaad208b5f

-- Sol generated from Shared/GradedTransitivity/Structure.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Definitions.Def_Shared_GradedTransitivity_Structure
import Theorems.Thm_GradedTransitivity_eval_one_numerator_of_eventually_const
import Theorems.Thm_GradedTransitivity_torbits_eq_one_iff

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




open GradedTransitivity in
theorem solution(r N : ℕ) (h : ∀ n ≥ N, IsRTransitive (G n) (Y n) r)
    {P : ℚ[X]} (hP : (1 - PowerSeries.X) * gen (hilbertSeq G Y r) = (P : PowerSeries ℚ)) :
    P.eval 1 = 1 := by
  refine eval_one_numerator_of_eventually_const (c := 1) (N := N) (fun n hn => ?_) hP
  simp only [hilbertSeq]
  rw [(torbits_eq_one_iff r).2 (h n hn)]
  norm_num
