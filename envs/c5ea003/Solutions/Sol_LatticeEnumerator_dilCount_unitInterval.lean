-- Prove2me | solution 1 for LatticeEnumerator.dilCount_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:02:42.759443+00:00
-- url     : https://prove2.me/submissions/f36dbf70-c71a-4efb-a5f6-91ee444d2c7b

-- Sol generated from Cryptography/LatticePointExamples.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness
import Theorems.Thm_LatticeEnumerator_mem_dilLattice

/-!
# Worked examples and computational sanity checks

Concrete evaluations of the lattice-point enumerator, used as machine-checked evidence that the
definitions in `Cryptography.LatticePointEnumerator` behave as intended.

## Main results

* `LatticeEnumerator.dilCount_unitInterval` : in dimension one, `L_{[0,1)}(t) = ⌈t⌉` for every
  `t > 0`; in particular `L(t)/t → 1 = vol([0,1))`, in agreement with the Gauss–Weyl theorem.
* `LatticeEnumerator.dilCount_unitInterval_examples` : numerical instances.
* `LatticeEnumerator.dilCount_empty`, `LatticeEnumerator.shiftCount_empty` : degenerate cases.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open LatticeEnumerator







open LatticeEnumerator in
theorem solution{t : ℝ} (ht : 0 < t) :
    dilCount (Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1) t = ⌈t⌉₊ := by
  have hset : dilLattice (Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1) t
      = (fun z : ℤ => (fun _ : Fin 1 => z)) '' (Set.Ico (0 : ℤ) ⌈t⌉) := by
    ext k
    simp only [mem_dilLattice, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ico,
      Set.mem_image]
    constructor
    · intro hk
      obtain ⟨h1, h2⟩ := hk 0
      refine ⟨k 0, ⟨?_, ?_⟩, ?_⟩
      · have : (0 : ℝ) ≤ (k 0 : ℝ) := by
          rw [le_div_iff₀ ht] at h1; linarith
        exact_mod_cast this
      · refine Int.lt_ceil.2 ?_
        rw [div_lt_one ht] at h2
        exact h2
      · funext i
        fin_cases i
        rfl
    · rintro ⟨z, ⟨hz0, hz1⟩, rfl⟩
      intro i
      refine ⟨?_, ?_⟩
      · have : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz0
        positivity
      · rw [div_lt_one ht]
        exact Int.lt_ceil.1 hz1
  have hinj : Function.Injective (fun z : ℤ => (fun _ : Fin 1 => z)) := by
    intro a b hab
    exact congrFun hab 0
  have hIco : (Set.Ico (0 : ℤ) ⌈t⌉) = ↑(Finset.Ico (0 : ℤ) ⌈t⌉) := by simp
  rw [dilCount, hset, Set.ncard_image_of_injective _ hinj, hIco, Set.ncard_coe_finset]
  have hceil : ((⌈t⌉₊ : ℕ) : ℤ) = ⌈t⌉ := Int.natCast_ceil_eq_ceil ht.le
  simp only [Int.card_Ico, sub_zero]
  omega
