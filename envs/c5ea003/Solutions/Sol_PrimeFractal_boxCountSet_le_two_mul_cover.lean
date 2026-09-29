-- Prove2me | solution 1 for PrimeFractal.boxCountSet_le_two_mul_cover
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:00:05.039242+00:00
-- url     : https://prove2.me/submissions/c36306b0-6abc-4fb4-a865-5f6484b78dbb

-- Sol generated from NumberTheory/PrimeFractalCovering.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalRefined

/-!
# Robustness of the box dimension: grid boxes versus arbitrary covers

`NumberTheory.PrimeFractalBoxDimension` computes the box dimension of the prime
fractal with *grid* boxes `[k/m, (k+1)/m)`.  A critic may object that the value
of a "dimension" must not depend on that choice.  It does not: an interval of
length `1/m` meets at most two grid boxes, so any cover of `S` by `K` intervals
of length `1/m` satisfies `boxCountSet S m ≤ 2 K`.

Consequently the dimension-`1` lower bound survives verbatim for the
covering-number definition of the Minkowski dimension
(`primeFractal_cover_card_ge`): however cleverly one covers the primes by
intervals of length `1/m`, one needs `m^{1-o(1)}` of them.
-/

open PrimeFractal

open Filter Topology




open PrimeFractal in
theorem solution{S : Set ℝ} {m : ℕ} {I : Set ℝ} (hIfin : I.Finite)
    (hcov : S ⊆ ⋃ c ∈ I, Set.Icc c (c + 1 / (m : ℝ))) :
    boxCountSet S m ≤ 2 * I.ncard := by
  classical
  set g : ℝ × ℕ → ℕ := fun q => ⌊(m : ℝ) * q.1⌋₊ + q.2 with hg
  have hfinprod : (I ×ˢ ({0, 1} : Set ℕ)).Finite := hIfin.prod (Set.toFinite _)
  have hsub : (fun x => ⌊(m : ℝ) * x⌋₊) '' S ⊆ g '' (I ×ˢ ({0, 1} : Set ℕ)) := by
    rintro k ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
    obtain ⟨hc1, hc2⟩ := hxt
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · refine ⟨(t, 0), ⟨ht, by simp⟩, ?_⟩
      simp [hg, hm0]
    · have hm0' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      have hlow : (m : ℝ) * t ≤ (m : ℝ) * x := by nlinarith
      have hhigh : (m : ℝ) * x ≤ (m : ℝ) * t + 1 := by
        have : (m : ℝ) * x ≤ (m : ℝ) * (t + 1 / (m : ℝ)) := by nlinarith
        calc (m : ℝ) * x ≤ (m : ℝ) * (t + 1 / (m : ℝ)) := this
          _ = (m : ℝ) * t + 1 := by field_simp
      have h1 : ⌊(m : ℝ) * t⌋₊ ≤ ⌊(m : ℝ) * x⌋₊ := Nat.floor_le_floor hlow
      have h2 : ⌊(m : ℝ) * x⌋₊ ≤ ⌊(m : ℝ) * t⌋₊ + 1 := by
        have hstep : ⌊(m : ℝ) * x⌋₊ ≤ ⌊(m : ℝ) * t + 1⌋₊ := Nat.floor_le_floor hhigh
        rcases le_or_gt 0 ((m : ℝ) * t) with hpos | hneg
        · rwa [Nat.floor_add_one hpos] at hstep
        · have : ⌊(m : ℝ) * t + 1⌋₊ = 0 := by
            apply Nat.floor_eq_zero.mpr
            linarith
          omega
      refine ⟨(t, ⌊(m : ℝ) * x⌋₊ - ⌊(m : ℝ) * t⌋₊), ⟨ht, ?_⟩, ?_⟩
      · have : ⌊(m : ℝ) * x⌋₊ - ⌊(m : ℝ) * t⌋₊ = 0 ∨ ⌊(m : ℝ) * x⌋₊ - ⌊(m : ℝ) * t⌋₊ = 1 := by
          omega
        rcases this with h | h <;> simp [h]
      · simp only [hg]
        omega
  have hfinimg : (g '' (I ×ˢ ({0, 1} : Set ℕ))).Finite := hfinprod.image _
  calc boxCountSet S m ≤ (g '' (I ×ˢ ({0, 1} : Set ℕ))).ncard :=
        Set.ncard_le_ncard hsub hfinimg
    _ ≤ (I ×ˢ ({0, 1} : Set ℕ)).ncard := Set.ncard_image_le hfinprod
    _ = I.ncard * ({0, 1} : Set ℕ).ncard := Set.ncard_prod
    _ = 2 * I.ncard := by
        rw [Set.ncard_pair (by norm_num)]
        ring
