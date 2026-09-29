-- Prove2me | solution 1 for GradedTransitivity.one_sub_X_mul_gen_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:51:03.010635+00:00
-- url     : https://prove2.me/submissions/c5096dbe-56c4-4f36-8dee-0d1498fd7a92

-- Sol generated from Shared/GradedTransitivity/GSet.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Theorems.Thm_GradedTransitivity_coeff_gen
import Theorems.Thm_GradedTransitivity_one_sub_X_mul_gen

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
theorem solution(N : ℕ) :
    (1 - PowerSeries.X) * gen (fun n => if N ≤ n then (1 : ℚ) else 0)
      = (PowerSeries.X : PowerSeries ℚ) ^ N := by
  rw [one_sub_X_mul_gen]
  ext n
  cases n with
  | zero =>
      simp only [map_add, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C,
        PowerSeries.coeff_X_pow, zero_add]
      by_cases hN : N = 0
      · simp [hN]
      · simp [hN]
        omega
  | succ m =>
      simp only [map_add, PowerSeries.coeff_succ_X_mul, coeff_gen, GradedTransitivity.sdiff,
        PowerSeries.coeff_C, PowerSeries.coeff_X_pow, Nat.succ_ne_zero, if_false, add_zero]
      by_cases h1 : N ≤ m
      · simp [h1, (by omega : N ≤ m + 1)]
        omega
      · by_cases h2 : N ≤ m + 1
        · have hmN : m + 1 = N := by omega
          simp [h1, hmN]
        · simp [h1, h2]
          omega
