-- Prove2me | solution 1 for lehmer_mahler_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:02:20.32003+00:00
-- url     : https://prove2.me/submissions/56bab87c-8d8b-4f3c-9f02-427e77c399e3

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

open Polynomial

private noncomputable def witness : Polynomial ℤ := X ^ 2 + C 2

private theorem witness_monic : witness.Monic :=
  monic_X_pow_add_C 2 (by decide)

private theorem witness_roots : witness.roots = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro z hz
  have hz' := (mem_roots witness_monic.ne_zero).mp hz
  have heq : z ^ 2 + 2 = 0 := by simpa [IsRoot, witness] using hz'
  nlinarith [sq_nonneg z]

private theorem witness_irreducible : Irreducible witness := by
  apply (witness_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [witness, natDegree_X_pow_add_C])
    (by rw [witness, natDegree_X_pow_add_C]; decide)).mpr witness_roots

private theorem witness_not_cyclotomic :
    ¬ ∃ n : ℕ, 1 ≤ n ∧ witness ∣ cyclotomic n ℤ := by
  rintro ⟨n, hn, hd⟩
  have he := Polynomial.eval_dvd (x := (0 : ℤ)) hd
  simp only [witness, eval_add, eval_pow, eval_X, zero_pow (by decide : 2 ≠ 0),
    eval_C, zero_add, ← coeff_zero_eq_eval_zero] at he
  by_cases h1 : n = 1
  · subst n
    norm_num [cyclotomic_one] at he
  · rw [cyclotomic_coeff_zero ℤ (by omega)] at he
    norm_num at he

theorem solution :
    ¬ ∃ c : ℝ, 1 < c ∧
      ∀ p : Polynomial ℤ, Irreducible p → p.Monic →
        (¬ ∃ n : ℕ, 1 ≤ n ∧ p ∣ Polynomial.cyclotomic n ℤ) →
        c ≤ Finset.univ.prod (fun z : p.roots.toFinset =>
          max 1 (Complex.normSq z)) := by
  rintro ⟨c, hc, h⟩
  have hh := h witness witness_irreducible witness_monic witness_not_cyclotomic
  letI : IsEmpty witness.roots.toFinset := ⟨fun z => by
    simpa [witness_roots] using z.property⟩
  have hc1 : c ≤ 1 := by simpa using hh
  exact (not_le_of_gt hc) hc1
