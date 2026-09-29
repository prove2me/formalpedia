-- Prove2me | solution 1 for PrimeFractal.sub_one_le_intBoxCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:18:53.312857+00:00
-- url     : https://prove2.me/submissions/1363948d-3f7d-4d0d-adda-a638a08e310e

-- Sol generated from NumberTheory/PrimeFractalIntegers.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalIntegers
import Theorems.Thm_PrimeFractal_boxIndex_le
import Theorems.Thm_PrimeFractal_boxIndex_lt

/-!
# The logarithmic lens cannot see primality

The same construction applied to *all* integers `≥ 2` produces the "integer
fractal" `{1 / log n : n ≥ 2}`.  We show it has

* Hausdorff dimension `0` (it is countable), and
* box-counting dimension `1` (`tendsto_intBoxCount_log_div`),

exactly like the prime fractal.  The proof of the lower bound is the same
separation estimate `boxIndex_lt`, but with no arithmetic input at all: for
integers one may simply count `Y - 1` of them below `Y`, where the primes needed
Chebyshev's theorem.

**Conclusion.** Both dimensions agree for the primes and for all integers, so
neither can detect primality: the mission's programme of reading off arithmetic
information (twin primes) from `dim (P, d)` is structurally impossible.  The
difference between the two sets is only visible in the second-order term (the
number of occupied boxes; see `NumberTheory.PrimeFractalRefined`).
-/

open PrimeFractal

open Filter Topology






theorem boxIndex_injOn_int {m Y : ℕ} (hm : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ m) :
    Set.InjOn (boxIndex m) {n : ℕ | 2 ≤ n ∧ n ≤ Y} := by
  rintro p ⟨hp, hpY⟩ q ⟨hq, hqY⟩ hpq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := boxIndex_lt hp hq hpY hqY h hm
    rw [hpq] at hlt
    exact lt_irrefl _ hlt
  · have hlt := boxIndex_lt hq hp hqY hpY h hm
    rw [hpq] at hlt
    exact lt_irrefl _ hlt

theorem ncard_int_interval (Y : ℕ) : {n : ℕ | 2 ≤ n ∧ n ≤ Y}.ncard = Y - 1 := by
  have hset : {n : ℕ | 2 ≤ n ∧ n ≤ Y} = ↑(Finset.Icc 2 Y) := by
    ext n
    simp
  rw [hset, Set.ncard_coe_finset, Nat.card_Icc]
  omega






open PrimeFractal in
theorem solution{m Y : ℕ} (hm : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ m) :
    Y - 1 ≤ intBoxCount m := by
  have hsub : boxIndex m '' {n : ℕ | 2 ≤ n ∧ n ≤ Y} ⊆ boxIndex m '' {n : ℕ | 2 ≤ n} := by
    rintro k ⟨p, hp, rfl⟩
    exact ⟨p, hp.1, rfl⟩
  have hfin : (boxIndex m '' {n : ℕ | 2 ≤ n}).Finite := by
    refine Set.Finite.subset (Finset.range (2 * m + 1)).finite_toSet ?_
    rintro k ⟨p, hp, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (boxIndex_le m p hp)
  calc Y - 1 = {n : ℕ | 2 ≤ n ∧ n ≤ Y}.ncard := (ncard_int_interval Y).symm
    _ = (boxIndex m '' {n : ℕ | 2 ≤ n ∧ n ≤ Y}).ncard :=
        (Set.InjOn.ncard_image (boxIndex_injOn_int hm)).symm
    _ ≤ (boxIndex m '' {n : ℕ | 2 ≤ n}).ncard := Set.ncard_le_ncard hsub hfin
    _ = intBoxCount m := rfl
