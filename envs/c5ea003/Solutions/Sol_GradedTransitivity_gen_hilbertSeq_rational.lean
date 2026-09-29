-- Prove2me | solution 1 for GradedTransitivity.gen_hilbertSeq_rational
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:49:09.09664+00:00
-- url     : https://prove2.me/submissions/f1f9036b-37ea-4953-8f69-7495d4be34ad

-- Sol generated from Shared/GradedTransitivity/GSet.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Theorems.Thm_GradedTransitivity_exists_poly_pow_mul_gen
import Theorems.Thm_GradedTransitivity_torbits_eq_one_iff

/-!
# Graded `G`-sets, `r`-transitivity, and rational Hilbert series

Let `Y = ⨆_n Y_n` be a graded `G`-set (a family of `G`-sets indexed by the
grade `n`).  Following Mathlib's `MulAction.IsMultiplyPretransitive`, the
`r`-tuple object of a `G`-set `Y` is the `G`-set `Fin r ↪ Y` of injective
`r`-tuples, and we write

`t_r(Y) = #(orbits of G on Fin r ↪ Y)`.

The grade `Y_n` is *`r`-transitive* when `G` acts transitively on the nonempty
set `Fin r ↪ Y_n`, which is exactly `t_r(Y_n) = 1`.

## Main results

* `torbits_eq_one_iff` : `t_r(Y) = 1` iff `Y` is `r`-transitive.
* `gen_torbits_rational` : if `Y_n` is `r`-transitive for all large `n` then
  `∑_n t_r(Y_n) qⁿ` is `P(q)/(1-q)^{r+1}` with `P` a polynomial; moreover
  the denominator can be taken to be the divisor `1-q` of `(1-q)^{r+1}`.
* `gen_torbits_eq_of_exactly` : the exact Hilbert series `q^N/(1-q)` in the
  clean case where the grades below `N` carry no injective `r`-tuple.
* `perm_graded_gen` : the symmetric-group family `Y_n = Fin n`,
  `G_n = Equiv.Perm (Fin n)` realises `∑_n t_r(Y_n) qⁿ = q^r/(1-q)`.

The companion file `BinomialGF` shows that the exponent `r+1` is optimal for
general polynomial growth, so the theorem here is a genuine strengthening in
the transitive regime: eventual `r`-transitivity forces denominator `1-q`.
-/

open GradedTransitivity

open Polynomial MulAction




variable {G : Type*} [Group G] {Y : Type*} [MulAction G Y]





/-! ### Rationality of the Hilbert series of a graded `G`-set -/

variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]






/-! ### The exact Hilbert series in the clean case -/



/-! ### A concrete graded `G`-set: the symmetric groups -/





open GradedTransitivity in
theorem solution(r N : ℕ) (h : ∀ n ≥ N, IsRTransitive (G n) (Y n) r) :
    ∃ P : ℚ[X], (1 - PowerSeries.X) * gen (hilbertSeq G Y r) = (P : PowerSeries ℚ) := by
  have hz : EventuallyZero (sdiff^[1] (hilbertSeq G Y r)) := by
    refine ⟨N, fun n hn => ?_⟩
    simp only [Function.iterate_one, GradedTransitivity.sdiff, hilbertSeq]
    rw [(torbits_eq_one_iff r).2 (h (n + 1) (by omega)),
      (torbits_eq_one_iff r).2 (h n hn)]
    ring
  obtain ⟨P, hP⟩ := exists_poly_pow_mul_gen 1 (hilbertSeq G Y r) hz
  exact ⟨P, by simpa using hP⟩
