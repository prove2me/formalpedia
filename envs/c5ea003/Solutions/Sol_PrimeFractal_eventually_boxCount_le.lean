-- Prove2me | solution 1 for PrimeFractal.eventually_boxCount_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:22:14.091775+00:00
-- url     : https://prove2.me/submissions/4019d058-cbdf-48ea-95ed-7d3e5dd929e7

-- Sol generated from NumberTheory/PrimeFractalRefined.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
import Definitions.Def_NumberTheory_PrimeFractalRefined
import Theorems.Thm_PrimeFractal_eventually_log_pow_le
import Theorems.Thm_PrimeFractal_eventually_primeCounting_le_nat
import Theorems.Thm_PrimeFractal_eventually_two_le_log
import Theorems.Thm_PrimeFractal_primeCounting_eq_ncard

/-!
# Refined box-counting: a universal ceiling and a logarithmic defect

Two refinements of `NumberTheory.PrimeFractalBoxDimension`.

## 1. A universal ceiling: no subset of `ℝ` can have box dimension `> 1`

`boxCountSet S m` counts the boxes of size `1/m` meeting a set `S ⊆ ℝ`.  For any
`S` contained in a bounded interval, `boxCountSet_le` gives
`boxCountSet S m ≤ ⌊c m⌋ + 1`, whence `boxDim_le_one_of_bounded`:

  for every `ε > 0`, eventually `log (boxCountSet S m) / log m ≤ 1 + ε`.

This settles the mission's `1 + ε` conjecture *structurally*: whatever the
twin primes do, a subset of the line has box dimension at most `1`.  The value
`ε = 0` is not an accident of the primes; it is forced by the ambient
dimension.  (The Hausdorff dimension is likewise `≤ 1`, and for the primes it
is in fact `0`.)

## 2. A logarithmic defect: `boxCount m = Θ(m / log m)`, not `Θ(m)`

Chebyshev's *upper* bound (from Mathlib) plus a splitting of the primes at `m`
gives `eventually_boxCount_le`: `boxCount m ≤ 5 m / log m`.  Hence
`tendsto_boxCount_div_self`: `boxCount m / m → 0`.  So although the box
dimension is exactly `1`, the prime fractal has *zero one-dimensional Minkowski
content*: it is a dimension-`1` set that occupies a vanishing fraction of the
boxes a genuine interval would occupy.  This is the precise sense in which the
primes "fill out a line" — only up to a logarithmic factor, and they carry no
length at all.
-/

open PrimeFractal

open Filter Topology

/-! ### 1. The universal ceiling -/







/-! ### 2. The logarithmic defect -/





open PrimeFractal in
theorem solution:
    ∀ᶠ m : ℕ in atTop, (boxCount m : ℝ) ≤ 5 * (m : ℝ) / Real.log m := by
  filter_upwards [eventually_primeCounting_le_nat, eventually_two_le_log,
    eventually_log_pow_le (C := 1) one_pos 1, eventually_ge_atTop 2] with m hpi hL2 hmlog hm2
  set L : ℝ := Real.log m with hLdef
  have hL0 : 0 < L := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmL : 1 ≤ (m : ℝ) / L := by
    rw [le_div_iff₀ hL0]
    simpa using hmlog
  set K : ℕ := ⌊(m : ℝ) / L⌋₊ with hKdef
  -- split the primes at `m`
  have hsplit : occupiedBoxes m ⊆
      boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ m} ∪ ↑(Finset.range (K + 1)) := by
    rintro k ⟨p, hp, rfl⟩
    by_cases hpm : p ≤ m
    · exact Or.inl ⟨p, ⟨hp, hpm⟩, rfl⟩
    · refine Or.inr ?_
      simp only [Finset.coe_range, Set.mem_Iio]
      refine Nat.lt_succ_of_le ?_
      have hpm' : (m : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_of_lt (not_le.mp hpm)
      have hmpos : (0 : ℝ) < (m : ℝ) := by
        have : (2 : ℕ) ≤ m := hm2
        exact_mod_cast lt_of_lt_of_le two_pos this
      have hlogp : L ≤ Real.log p := by
        rw [hLdef]; exact Real.log_le_log hmpos hpm'
      have hle : (m : ℝ) * logInv p ≤ (m : ℝ) / L := by
        rw [logInv, mul_one_div, div_le_div_iff_of_pos_left hmpos (by linarith) hL0]
        exact hlogp
      exact Nat.floor_le_floor hle
  have hfinA : {p : ℕ | p.Prime ∧ p ≤ m}.Finite :=
    Set.Finite.subset (Set.finite_Iic m) (fun p hp => hp.2)
  have hfin : (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ m} ∪
      ↑(Finset.range (K + 1)) : Set ℕ).Finite :=
    (hfinA.image _).union (Finset.range (K + 1)).finite_toSet
  have hcard : boxCount m ≤ Nat.primeCounting m + (K + 1) := by
    have h1 := Set.ncard_le_ncard hsplit hfin
    have h2 := Set.ncard_union_le (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ m})
      (↑(Finset.range (K + 1)) : Set ℕ)
    have h3 : (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ m}).ncard ≤ Nat.primeCounting m := by
      calc (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ m}).ncard
          ≤ {p : ℕ | p.Prime ∧ p ≤ m}.ncard := Set.ncard_image_le hfinA
        _ = Nat.primeCounting m := primeCounting_eq_ncard m
    have h4 : ((Finset.range (K + 1) : Finset ℕ) : Set ℕ).ncard = K + 1 := by
      simp
    calc boxCount m ≤ (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ m} ∪
            ↑(Finset.range (K + 1))).ncard := h1
      _ ≤ (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ m}).ncard +
            ((Finset.range (K + 1) : Finset ℕ) : Set ℕ).ncard := h2
      _ ≤ Nat.primeCounting m + (K + 1) := by rw [h4]; exact Nat.add_le_add_right h3 _
  have hKle : (K : ℝ) ≤ (m : ℝ) / L := Nat.floor_le (by positivity)
  have hcard' : (boxCount m : ℝ) ≤ (Nat.primeCounting m : ℝ) + ((K : ℝ) + 1) := by
    exact_mod_cast hcard
  have : (boxCount m : ℝ) ≤ 2.4 * (m : ℝ) / L + (m : ℝ) / L + 1 := by
    linarith [hpi, hKle]
  have hfive : 2.4 * (m : ℝ) / L + (m : ℝ) / L + 1 ≤ 5 * (m : ℝ) / L := by
    have h1 : 2.4 * (m : ℝ) / L = 2.4 * ((m : ℝ) / L) := by ring
    have h2 : 5 * (m : ℝ) / L = 5 * ((m : ℝ) / L) := by ring
    rw [h1, h2]
    linarith [hmL]
  linarith
