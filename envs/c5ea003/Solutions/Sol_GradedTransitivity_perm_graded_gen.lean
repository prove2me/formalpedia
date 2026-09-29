-- Prove2me | solution 1 for GradedTransitivity.perm_graded_gen
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:52:47.362287+00:00
-- url     : https://prove2.me/submissions/c265505b-4062-4e85-9411-5c89e9822742

-- Sol generated from Shared/GradedTransitivity/GSet.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Theorems.Thm_GradedTransitivity_one_sub_X_mul_gen_step
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



/-- If there is no injective `r`-tuple at all, `t_r(Y) = 0`. -/
theorem torbits_eq_zero (r : ℕ) (h : IsEmpty (Fin r ↪ Y)) : torbits G Y r = 0 := by
  have hE : IsEmpty (MulAction.orbitRel.Quotient G (Fin r ↪ Y)) := by
    constructor
    intro q
    induction q using Quotient.inductionOn with
    | h a => exact h.elim a
  exact Nat.card_eq_zero.2 (Or.inl hE)


/-! ### Rationality of the Hilbert series of a graded `G`-set -/

variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]






/-! ### The exact Hilbert series in the clean case -/


/-- If every grade `≥ N` is `r`-transitive and every grade `< N` carries no
injective `r`-tuple, the Hilbert series is *exactly* `q^N/(1-q)`. -/
theorem gen_hilbertSeq_eq_of_exactly (r N : ℕ)
    (h : ∀ n ≥ N, IsRTransitive (G n) (Y n) r)
    (h' : ∀ n < N, IsEmpty (Fin r ↪ Y n)) :
    (1 - PowerSeries.X) * gen (hilbertSeq G Y r) = (PowerSeries.X : PowerSeries ℚ) ^ N := by
  have hseq : hilbertSeq G Y r = fun n => if N ≤ n then (1 : ℚ) else 0 := by
    funext n
    by_cases hn : N ≤ n
    · simp only [hilbertSeq, hn, if_true]
      rw [(torbits_eq_one_iff r).2 (h n hn)]
      norm_num
    · simp only [hilbertSeq, hn, if_false]
      rw [torbits_eq_zero r (h' n (by omega))]
      norm_num
  rw [hseq, one_sub_X_mul_gen_step]

/-! ### A concrete graded `G`-set: the symmetric groups -/

/-- Each grade of the symmetric-group family `Y_n = Fin n`,
`G_n = Equiv.Perm (Fin n)` is `r`-transitive as soon as `r ≤ n`. -/
theorem perm_isRTransitive (r n : ℕ) (h : r ≤ n) :
    IsRTransitive (Equiv.Perm (Fin n)) (Fin n) r := by
  refine ⟨Equiv.Perm.isMultiplyPretransitive (Fin n) r, ?_⟩
  exact ⟨⟨fun i => ⟨(i : ℕ), lt_of_lt_of_le i.2 h⟩, by
    intro i j hij
    simpa [Fin.ext_iff] using hij⟩⟩

/-- Below the diagonal there is no injective `r`-tuple in `Fin n`. -/
theorem perm_isEmpty (r n : ℕ) (h : n < r) : IsEmpty (Fin r ↪ Fin n) := by
  constructor
  intro f
  have := Fintype.card_le_of_injective f f.injective
  simp only [Fintype.card_fin] at this
  omega



open GradedTransitivity in
theorem solution(r : ℕ) :
    (1 - PowerSeries.X) *
        gen (hilbertSeq (fun n => Equiv.Perm (Fin n)) (fun n => Fin n) r)
      = (PowerSeries.X : PowerSeries ℚ) ^ r :=
  gen_hilbertSeq_eq_of_exactly r r (fun n hn => perm_isRTransitive r n hn)
    (fun n hn => perm_isEmpty r n hn)
