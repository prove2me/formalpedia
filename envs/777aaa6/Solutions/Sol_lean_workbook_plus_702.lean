-- Prove2me | solution 1 for lean_workbook_plus_702
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:22:14.223264+00:00
-- url     : https://prove2.me/submissions/8e4a41e2-f24e-42ab-ae30-bd0ffc961b58

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ring

namespace CoprimeExponentPositiveSolutions

theorem scaling_exponents (A B C : ℕ) (hC : C ≠ 0)
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C) :
    ∃ u v w L : ℕ, u * A = L ∧ v * B = L ∧ w * C = L + 1 := by
  obtain ⟨L, hL0, hLC⟩ := Nat.chineseRemainder (hAC.mul_left hBC) 0 (C - 1)
  have hprod : A * B ∣ L := Nat.modEq_zero_iff_dvd.mp hL0
  have hA : A ∣ L := (show A ∣ A * B from ⟨B, rfl⟩).trans hprod
  have hB : B ∣ L := (show B ∣ A * B from ⟨A, by ring⟩).trans hprod
  have hC1 : 1 ≤ C := Nat.one_le_iff_ne_zero.mpr hC
  have hplus : L + 1 ≡ C [MOD C] := by
    simpa only [Nat.sub_add_cancel hC1] using hLC.add_right 1
  have hCdiv : C ∣ L + 1 := Nat.modEq_zero_iff_dvd.mp
    (hplus.trans ((dvd_refl C).modEq_zero_nat))
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hB
  obtain ⟨w, hw⟩ := hCdiv
  exact ⟨u, v, w, L, by simpa [mul_comm] using hu.symm,
    by simpa [mul_comm] using hv.symm, by simpa [mul_comm] using hw.symm⟩

theorem scaling_identity (A B C u v w L t : ℕ)
    (hu : u * A = L) (hv : v * B = L) (hw : w * C = L + 1) :
    (t * (t ^ A + 1) ^ u) ^ A + ((t ^ A + 1) ^ v) ^ B =
      ((t ^ A + 1) ^ w) ^ C := by
  simp only [mul_pow, ← pow_mul, hu, hv, hw]
  rw [pow_succ]
  ring

theorem arbitrarily_large (A B C : ℕ) (hC : C ≠ 0)
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C) (t : ℕ) (ht : 0 < t) :
    ∃ x y z : ℕ, t ≤ x ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ A + y ^ B = z ^ C := by
  obtain ⟨u, v, w, L, hu, hv, hw⟩ := scaling_exponents A B C hC hAC hBC
  let N := t ^ A + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hNu : 0 < N ^ u := pow_pos hN u
  refine ⟨t * N ^ u, N ^ v, N ^ w, ?_, Nat.mul_pos ht hNu,
    pow_pos hN v, pow_pos hN w, ?_⟩
  · simpa using Nat.mul_le_mul_left t (show 1 ≤ N ^ u from hNu)
  · exact scaling_identity A B C u v w L t hu hv hw

theorem infinite_positive_solutions (A B C : ℕ) (hC : C ≠ 0)
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C) :
    {p : ℕ × ℕ × ℕ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
      p.1 ^ A + p.2.1 ^ B = p.2.2 ^ C}.Infinite := by
  intro hf
  obtain ⟨K, hK⟩ := (hf.image (fun p => p.1)).bddAbove
  obtain ⟨x, y, z, hxK, hx, hy, hz, heq⟩ :=
    arbitrarily_large A B C hC hAC hBC (K + 1) (by omega)
  have hbound : x ≤ K := hK ⟨(x, y, z), ⟨hx, hy, hz, heq⟩, rfl⟩
  omega

end CoprimeExponentPositiveSolutions

theorem solution (A B C : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hABC : Nat.Coprime A B) (hABC' : Nat.Coprime A C) (hABC'' : Nat.Coprime B C) :
    ∃ x y z : ℕ, x ^ A + y ^ B = z ^ C := by
  obtain ⟨⟨x, y, z⟩, _, _, _, heq⟩ :=
    (CoprimeExponentPositiveSolutions.infinite_positive_solutions A B C hC hABC' hABC'').nonempty
  exact ⟨x, y, z, heq⟩
