-- Prove2me | solution 1 for BerggrenSpectral.berg_two_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:29.4379+00:00
-- url     : https://prove2.me/submissions/de22a241-32bc-4238-80d7-a2f4525fa425

-- Thm stub generated from Cryptography/BerggrenSpectral/SpectrumAndTrace.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_SpectrumAndTrace
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance

/-!
# The Exact Resonance Spectrum and the Berggren–Lucas Trace Sequence

Second research cycle.  Where `HyperbolicResonance.lean` produced *sufficient* resonant
frequencies, this file determines the resonance set **exactly**, decomposes it across the
factors of a semiprime modulus, and extracts an arithmetic sequence — the *Berggren–Lucas
trace sequence* — carrying a Fermat-type congruence.

## Main results

* `berg_two_pow_eq_one_iff` : modulo an odd prime `p`,
  `M₂ ^ k ≡ 1 ⟺ U ^ k = 1 ∧ k even`, where `U = !![3,2;4,3]` is the hyperbolic block.
  This is an exact description of the resonance spectrum, not merely a divisibility bound.
* `berg_two_orderOf` : `ord_p(M₂) = lcm (2, ord_p(U))`.
* `berg_resonance_crt` : for coprime moduli the resonance sets intersect,
  `M₂ ^ k ≡ 1 (mod m n) ⟺ M₂ ^ k ≡ 1 (mod m) ∧ M₂ ^ k ≡ 1 (mod n)`.  Factoring `N = p q`
  is therefore exactly the problem of *separating two resonant frequencies inside one
  modulus*, which is the conceptual content of `Factorization.lean`.
* `berg_trace_rec`, `berg_trace_values` : the traces `t k = tr (M₂ ^ k)` satisfy the
  Newton recurrence `t (k+3) = 5 t (k+2) + 5 t (k+1) - t k` of the characteristic
  polynomial, with `t 0, t 1, t 2, t 3 = 3, 5, 35, 197`.
* `berg_trace_fermat` : for every odd prime `p`, `t p ≡ 5 (mod p)` — a Fermat/Lucas-type
  congruence for the Berggren tree, proved from the matrix Frobenius, *not* from a
  hypothetical eigenvalue computation.
* `berg_trace_composite_witness` : the contrapositive is a compositeness test;
  `berg_nine_composite_witness` runs it on `N = 9`.
-/

open BerggrenSpectral

open Matrix

variable (p : ℕ) [Fact p.Prime]

/-! ## The exact resonance spectrum modulo a prime -/

open Matrix Polynomial
open Matrix
namespace BerggrenSpectral

theorem det_M₁ : M₁.det = 1 := by simp [M₁, Matrix.det_fin_three]

end BerggrenSpectral

namespace BerggrenSpectral

theorem det_M₂ : M₂.det = -1 := by simp [M₂, Matrix.det_fin_three]

end BerggrenSpectral

namespace BerggrenSpectral

theorem det_M₃ : M₃.det = 1 := by simp [M₃, Matrix.det_fin_three]

end BerggrenSpectral

namespace BerggrenSpectral

theorem trace_M₁ : Matrix.trace M₁ = 3 := by simp [M₁, Matrix.trace_fin_three]

end BerggrenSpectral

namespace BerggrenSpectral

theorem trace_M₂ : Matrix.trace M₂ = 5 := by simp [M₂, Matrix.trace_fin_three]

end BerggrenSpectral

namespace BerggrenSpectral

theorem trace_M₃ : Matrix.trace M₃ = 3 := by simp [M₃, Matrix.trace_fin_three]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_charpoly_one : M₁.charpoly = (X - 1) ^ 3 := by
  simp [Matrix.charpoly, M₁, Matrix.det_fin_three, charmatrix]
  ring

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_charpoly_three : M₃.charpoly = (X - 1) ^ 3 := by
  simp [Matrix.charpoly, M₃, Matrix.det_fin_three, charmatrix]
  ring

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_charpoly_two : M₂.charpoly = (X + 1) * (X ^ 2 - 6 * X + 1) := by
  simp [Matrix.charpoly, M₂, Matrix.det_fin_three, charmatrix]
  ring

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_nilpotent_one : (M₁ - 1) ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M₁, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_nilpotent_three : (M₃ - 1) ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M₃, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_nilpotent_one_sq_ne : (M₁ - 1) ^ 2 ≠ 0 := by
  intro h
  have h22 := congrFun (congrFun h 1) 1
  simp [M₁, pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at h22

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_nilpotent_three_sq_ne : (M₃ - 1) ^ 2 ≠ 0 := by
  intro h
  have h22 := congrFun (congrFun h 0) 0
  simp [M₃, pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at h22

end BerggrenSpectral

namespace BerggrenSpectral

theorem bergSilver_sq : bergSilver = (⟨1, 1⟩ : ℤ√2) ^ 2 := by
  ext <;> simp [bergSilver, pow_two]

end BerggrenSpectral

namespace BerggrenSpectral

theorem bergSilver_norm : Zsqrtd.norm bergSilver = 1 := by
  simp [bergSilver, Zsqrtd.norm]

end BerggrenSpectral

namespace BerggrenSpectral

theorem bergSilver_isRoot : bergSilver ^ 2 - 6 * bergSilver + 1 = 0 := by
  ext <;> simp [bergSilver, pow_two]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_real_eigenvalue :
    (3 + 2 * Real.sqrt 2) ^ 2 - 6 * (3 + 2 * Real.sqrt 2) + 1 = 0 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_eigenvalue_mul : (3 + 2 * Real.sqrt 2) * (3 - 2 * Real.sqrt 2) = 1 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_two_eigenvector :
    M₂ *ᵥ ![1, -1, 0] = (-1 : ℤ) • ![1, -1, 0] := by
  funext i
  fin_cases i <;> simp [M₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_two_symm : M₂.transpose = M₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M₂]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_two_minpoly : (M₂ + 1) * (M₂ ^ 2 - (6 : ℤ) • M₂ + 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M₂, pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_two_minpoly_proper : M₂ + 1 ≠ 0 ∧ M₂ ^ 2 - (6 : ℤ) • M₂ + 1 ≠ 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [M₂] at h00
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [M₂, pow_two] at h00

end BerggrenSpectral

namespace BerggrenSpectral

theorem redMat_pow (m : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) (k : ℕ) :
    redMat m (A ^ k) = (redMat m A) ^ k := map_pow _ _ _

end BerggrenSpectral

namespace BerggrenSpectral

theorem redMat_apply (m : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) :
    redMat m A i j = ((A i j : ℤ) : ZMod m) := rfl

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_one_pow (k : ℕ) :
    M₁ ^ k = !![1, -2 * (k : ℤ), 2 * (k : ℤ);
                2 * (k : ℤ), 1 - 2 * (k : ℤ) ^ 2, 2 * (k : ℤ) ^ 2;
                2 * (k : ℤ), -2 * (k : ℤ) ^ 2, 1 + 2 * (k : ℤ) ^ 2] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M₁, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_three_pow (k : ℕ) :
    M₃ ^ k = !![1 - 2 * (k : ℤ) ^ 2, 2 * (k : ℤ), 2 * (k : ℤ) ^ 2;
                -2 * (k : ℤ), 1, 2 * (k : ℤ);
                -2 * (k : ℤ) ^ 2, 2 * (k : ℤ), 1 + 2 * (k : ℤ) ^ 2] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M₃, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_one_pow_eq_one_iff (m k : ℕ) (hm : Odd m) :
    (redMat m M₁) ^ k = 1 ↔ m ∣ k := by
  constructor
  · intro h
    have h' : redMat m (M₁ ^ k) = 1 := by rw [BerggrenSpectral.redMat_pow]; exact h
    have hentry := congrFun (congrFun h' 0) 1
    rw [BerggrenSpectral.redMat_apply, BerggrenSpectral.berg_one_pow] at hentry
    have h2 : ((-2 * (k : ℤ) : ℤ) : ZMod m) = 0 := by simpa [Matrix.one_apply] using hentry
    have hd : (m : ℤ) ∣ (-2 * (k : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp h2
    have hd2 : (m : ℤ) ∣ 2 * (k : ℤ) := (dvd_neg).mp (by simpa [neg_mul] using hd)
    have hnat : m ∣ 2 * k := by exact_mod_cast hd2
    exact (Nat.coprime_two_right.mpr hm).dvd_of_dvd_mul_left hnat
  · rintro ⟨t, rfl⟩
    rw [← BerggrenSpectral.redMat_pow, BerggrenSpectral.berg_one_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [redMat]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_three_pow_eq_one_iff (m k : ℕ) (hm : Odd m) :
    (redMat m M₃) ^ k = 1 ↔ m ∣ k := by
  constructor
  · intro h
    have h' : redMat m (M₃ ^ k) = 1 := by rw [BerggrenSpectral.redMat_pow]; exact h
    have hentry := congrFun (congrFun h' 0) 1
    rw [BerggrenSpectral.redMat_apply, BerggrenSpectral.berg_three_pow] at hentry
    have h2 : ((2 * (k : ℤ) : ℤ) : ZMod m) = 0 := by simpa [Matrix.one_apply] using hentry
    have hd : (m : ℤ) ∣ 2 * (k : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp h2
    have hnat : m ∣ 2 * k := by exact_mod_cast hd
    exact (Nat.coprime_two_right.mpr hm).dvd_of_dvd_mul_left hnat
  · rintro ⟨t, rfl⟩
    rw [← BerggrenSpectral.redMat_pow, BerggrenSpectral.berg_three_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [redMat]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_one_orderOf (m : ℕ) (hm : Odd m) (hpos : 0 < m) :
    orderOf (redMat m M₁) = m := by
  refine (orderOf_eq_iff hpos).mpr ⟨(BerggrenSpectral.berg_one_pow_eq_one_iff m m hm).mpr dvd_rfl, ?_⟩
  intro n hn hn0 hcon
  exact absurd (Nat.le_of_dvd hn0 ((BerggrenSpectral.berg_one_pow_eq_one_iff m n hm).mp hcon)) (not_le.mpr hn)

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_three_orderOf (m : ℕ) (hm : Odd m) (hpos : 0 < m) :
    orderOf (redMat m M₃) = m := by
  refine (orderOf_eq_iff hpos).mpr ⟨(BerggrenSpectral.berg_three_pow_eq_one_iff m m hm).mpr dvd_rfl, ?_⟩
  intro n hn hn0 hcon
  exact absurd (Nat.le_of_dvd hn0 ((BerggrenSpectral.berg_three_pow_eq_one_iff m n hm).mp hcon)) (not_le.mpr hn)

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_one_orderOf_semiprime (p q : ℕ) (hp : Odd p) (hq : Odd q) (hp0 : 0 < p)
    (hq0 : 0 < q) : orderOf (redMat (p * q) M₁) = p * q :=
  berg_one_orderOf _ (hp.mul hq) (Nat.mul_pos hp0 hq0)

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_one_entries (k : ℕ) (i j : Fin 3) :
    (M₁ ^ k - 1) i j = 0 ∨ (M₁ ^ k - 1) i j = 2 * (k : ℤ) ∨ (M₁ ^ k - 1) i j = -2 * (k : ℤ) ∨
      (M₁ ^ k - 1) i j = 2 * (k : ℤ) ^ 2 ∨ (M₁ ^ k - 1) i j = -2 * (k : ℤ) ^ 2 := by
  rw [BerggrenSpectral.berg_one_pow]
  fin_cases i <;> fin_cases j <;> simp

end BerggrenSpectral

namespace BerggrenSpectral

private theorem gcd_dvd_gcd_sq {N k : ℕ} (hN : Odd N) {x : ℤ}
    (hx : x = 2 * (k : ℤ) ∨ x = -2 * (k : ℤ) ∨ x = 2 * (k : ℤ) ^ 2 ∨ x = -2 * (k : ℤ) ^ 2) :
    Int.gcd x (N : ℤ) ∣ Nat.gcd (k ^ 2) N := by
  set g := Int.gcd x (N : ℤ) with hg
  have hgN : g ∣ N := by exact_mod_cast Int.gcd_dvd_right x (N : ℤ)
  have hgx : (g : ℤ) ∣ x := Int.gcd_dvd_left x (N : ℤ)
  have hk2 : (g : ℤ) ∣ 2 * (k : ℤ) ^ 2 := by
    rcases hx with h | h | h | h <;> rw [h] at hgx
    · exact hgx.trans ⟨(k : ℤ), by ring⟩
    · exact hgx.trans ⟨-(k : ℤ), by ring⟩
    · exact hgx
    · exact hgx.trans ⟨-1, by ring⟩
  have hnat : g ∣ 2 * k ^ 2 := by exact_mod_cast hk2
  have hg2 : Nat.Coprime g 2 := Nat.Coprime.coprime_dvd_left hgN (Nat.coprime_two_right.mpr hN)
  exact Nat.dvd_gcd (hg2.dvd_of_dvd_mul_left hnat) hgN

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_one_gcd_barrier (N k : ℕ) (hN : Odd N) (i j : Fin 3)
    (h : (M₁ ^ k - 1) i j ≠ 0) :
    Int.gcd ((M₁ ^ k - 1) i j) (N : ℤ) ∣ Nat.gcd (k ^ 2) N := by
  rcases BerggrenSpectral.berg_one_entries k i j with h0 | hx
  · exact absurd h0 h
  · exact BerggrenSpectral.gcd_dvd_gcd_sq hN hx

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_one_no_advantage (N k : ℕ) (hN : Odd N) (i j : Fin 3)
    (h : (M₁ ^ k - 1) i j ≠ 0) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Int.gcd ((M₁ ^ k - 1) i j) (N : ℤ)) : r ∣ k ∧ r ∣ N := by
  have h1 := hdvd.trans (BerggrenSpectral.berg_one_gcd_barrier N k hN i j h)
  exact ⟨hr.dvd_of_dvd_pow (h1.trans (Nat.gcd_dvd_left _ _)), h1.trans (Nat.gcd_dvd_right _ _)⟩

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem blockEmbed_mul (A B : Matrix (Fin 2) (Fin 2) R) (c d : R) :
    blockEmbed R A c * blockEmbed R B d = blockEmbed R (A * B) (c * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockEmbed, Matrix.mul_apply, Fin.sum_univ_succ]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem blockEmbed_one : blockEmbed R (1 : Matrix (Fin 2) (Fin 2) R) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockEmbed]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem bergV_eq : bergV R = blockEmbed R (bergU R) (-1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bergV, blockEmbed, bergU]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem bergV_pow (k : ℕ) : (bergV R) ^ k = blockEmbed R ((bergU R) ^ k) ((-1 : R) ^ k) := by
  induction k with
  | zero => simpa using (BerggrenSpectral.blockEmbed_one (R := R)).symm
  | succ n ih => rw [pow_succ, ih, BerggrenSpectral.bergV_eq, BerggrenSpectral.blockEmbed_mul, ← pow_succ, ← pow_succ]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem berg_conj : M2R R * bergW R = bergW R * bergV R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M2R, bergW, bergV, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem berg_pow_conj (k : ℕ) : (M2R R) ^ k * bergW R = bergW R * (bergV R) ^ k := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, mul_assoc, BerggrenSpectral.berg_conj, ← mul_assoc, ih, mul_assoc]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem det_bergW : (bergW R).det = 2 := by
  rw [bergW, Matrix.det_fin_three]
  simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  ring

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem bergS_sq : (bergS R) ^ 2 = (8 : R) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bergS, pow_two, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem bergU_eq : bergU R = (3 : R) • 1 + bergS R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bergU, bergS]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem bergU_inv : bergU R * ((6 : R) • 1 - bergU R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bergU, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}

theorem det_bergU : (bergU R).det = 1 := by simp [bergU, Matrix.det_fin_two]; ring

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem bergU_frob (hp : p ≠ 2) :
    (bergU (ZMod p)) ^ p = (3 : ZMod p) • 1 + ((8 : ZMod p) ^ ((p - 1) / 2)) • bergS (ZMod p) := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  have hp1 : p = 2 * ((p - 1) / 2) + 1 := by obtain ⟨t, ht⟩ := hodd; omega
  have hcomm : Commute ((3 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) (bergS (ZMod p)) := by
    simp [Commute, SemiconjBy]
  have hSp : bergS (ZMod p) ^ p = ((8 : ZMod p) ^ ((p - 1) / 2)) • bergS (ZMod p) := by
    have h1 : bergS (ZMod p) ^ p = bergS (ZMod p) ^ (2 * ((p - 1) / 2) + 1) := by rw [← hp1]
    rw [h1, pow_succ, pow_mul, BerggrenSpectral.bergS_sq, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul]
  rw [BerggrenSpectral.bergU_eq, add_pow_char_of_commute _ hcomm, _root_.smul_pow, one_pow, ZMod.pow_card, hSp]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem eight_pow_eq_two_pow :
    (8 : ZMod p) ^ ((p - 1) / 2) = ((2 : ZMod p) ^ ((p - 1) / 2)) ^ 3 := by
  rw [show (8 : ZMod p) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem two_ne_zero_of_odd_prime (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
  have hd : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2
  have hd' : p ∣ 2 := by exact_mod_cast hd
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd')

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem two_chi_sq (hp : p ≠ 2) : ((2 : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  have hp1 : 2 * ((p - 1) / 2) = p - 1 := by obtain ⟨t, ht⟩ := hodd; omega
  rw [← pow_mul, mul_comm, hp1]
  exact ZMod.pow_card_sub_one_eq_one (BerggrenSpectral.two_ne_zero_of_odd_prime p hp)

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem bergU_pow_qr (hp : p ≠ 2) (h : (2 : ZMod p) ^ ((p - 1) / 2) = 1) :
    (bergU (ZMod p)) ^ (p - 1) = 1 := by
  have hp0 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le.trans' (by norm_num)
  have hfrob : (bergU (ZMod p)) ^ p = bergU (ZMod p) := by
    rw [BerggrenSpectral.bergU_frob p hp, BerggrenSpectral.eight_pow_eq_two_pow p, h, one_pow, one_smul, ← BerggrenSpectral.bergU_eq]
  have hsucc : (bergU (ZMod p)) ^ (p - 1) * bergU (ZMod p) = (bergU (ZMod p)) ^ p := by
    rw [← pow_succ]; congr 1; omega
  calc (bergU (ZMod p)) ^ (p - 1)
      = (bergU (ZMod p)) ^ (p - 1) * (bergU (ZMod p) * ((6 : ZMod p) • 1 - bergU (ZMod p))) := by
        rw [BerggrenSpectral.bergU_inv, mul_one]
    _ = ((bergU (ZMod p)) ^ (p - 1) * bergU (ZMod p)) * ((6 : ZMod p) • 1 - bergU (ZMod p)) := by
        rw [mul_assoc]
    _ = bergU (ZMod p) * ((6 : ZMod p) • 1 - bergU (ZMod p)) := by rw [hsucc, hfrob]
    _ = 1 := BerggrenSpectral.bergU_inv

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem bergU_pow_nqr (hp : p ≠ 2) (h : (2 : ZMod p) ^ ((p - 1) / 2) = -1) :
    (bergU (ZMod p)) ^ (p + 1) = 1 := by
  have hfrob : (bergU (ZMod p)) ^ p = (6 : ZMod p) • 1 - bergU (ZMod p) := by
    rw [BerggrenSpectral.bergU_frob p hp, BerggrenSpectral.eight_pow_eq_two_pow p, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bergS, bergU] <;> ring
  rw [pow_succ, hfrob, sub_mul, smul_mul_assoc, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bergU] <;> ring

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem sq_sub_one_nat (n : ℕ) : n ^ 2 - 1 = (n - 1) * (n + 1) := by
  cases n with
  | zero => rfl
  | succ m => simp only [Nat.add_sub_cancel]; exact (Nat.sub_eq_of_eq_add (by ring))

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem M2R_pow_eq_one (hp : p ≠ 2) {k : ℕ} (hU : (bergU (ZMod p)) ^ k = 1) (hk : Even k) :
    (M2R (ZMod p)) ^ k = 1 := by
  have hdet : IsUnit (bergW (ZMod p)).det := by
    rw [BerggrenSpectral.det_bergW]
    exact (isUnit_iff_ne_zero).mpr (BerggrenSpectral.two_ne_zero_of_odd_prime p hp)
  haveI : Invertible (bergW (ZMod p)) := invertibleOfIsUnitDet _ hdet
  have hV : (bergV (ZMod p)) ^ k = 1 := by
    rw [BerggrenSpectral.bergV_pow, hU, hk.neg_one_pow, BerggrenSpectral.blockEmbed_one]
  have h := BerggrenSpectral.berg_pow_conj (R := ZMod p) k
  rw [hV, mul_one] at h
  have h1 : (M2R (ZMod p)) ^ k * bergW (ZMod p) = 1 * bergW (ZMod p) := by rw [h, one_mul]
  exact mul_left_injective_of_invertible (bergW (ZMod p)) h1

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem redMat_M₂ (m : ℕ) : redMat m M₂ = M2R (ZMod m) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [redMat, M₂, M2R]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem even_sub_one (hp : p ≠ 2) : Even (p - 1) := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  obtain ⟨t, ht⟩ := hodd
  exact ⟨t, by omega⟩

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem even_add_one (hp : p ≠ 2) : Even (p + 1) := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  obtain ⟨t, ht⟩ := hodd
  exact ⟨t + 1, by omega⟩

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem berg_two_resonance_qr (hp : p ≠ 2) (h : (2 : ZMod p) ^ ((p - 1) / 2) = 1) :
    (redMat p M₂) ^ (p - 1) = 1 := by
  rw [BerggrenSpectral.redMat_M₂]
  exact BerggrenSpectral.M2R_pow_eq_one p hp (BerggrenSpectral.bergU_pow_qr p hp h) (BerggrenSpectral.even_sub_one p hp)

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem berg_two_resonance_nqr (hp : p ≠ 2) (h : (2 : ZMod p) ^ ((p - 1) / 2) = -1) :
    (redMat p M₂) ^ (p + 1) = 1 := by
  rw [BerggrenSpectral.redMat_M₂]
  exact BerggrenSpectral.M2R_pow_eq_one p hp (BerggrenSpectral.bergU_pow_nqr p hp h) (BerggrenSpectral.even_add_one p hp)

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem two_chi_cases (hp : p ≠ 2) :
    (2 : ZMod p) ^ ((p - 1) / 2) = 1 ∨ (2 : ZMod p) ^ ((p - 1) / 2) = -1 := by
  have h := BerggrenSpectral.two_chi_sq p hp
  have : ((2 : ZMod p) ^ ((p - 1) / 2) - 1) * ((2 : ZMod p) ^ ((p - 1) / 2) + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (by linear_combination h1)

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem berg_two_resonance (hp : p ≠ 2) : (redMat p M₂) ^ (p ^ 2 - 1) = 1 := by
  rcases BerggrenSpectral.two_chi_cases p hp with h | h
  · obtain ⟨t, ht⟩ : (p - 1) ∣ (p ^ 2 - 1) := ⟨p + 1, BerggrenSpectral.sq_sub_one_nat p⟩
    rw [ht, pow_mul, BerggrenSpectral.berg_two_resonance_qr p hp h, one_pow]
  · obtain ⟨t, ht⟩ : (p + 1) ∣ (p ^ 2 - 1) := ⟨p - 1, by rw [BerggrenSpectral.sq_sub_one_nat p]; ring⟩
    rw [ht, pow_mul, BerggrenSpectral.berg_two_resonance_nqr p hp h, one_pow]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (R : Type*) [CommRing R]
variable {R}
variable (p : ℕ) [Fact p.Prime]

theorem berg_two_resonance_mod_eight (hp : p ≠ 2) :
    (p % 8 = 1 ∨ p % 8 = 7 → (redMat p M₂) ^ (p - 1) = 1) ∧
    (p % 8 = 3 ∨ p % 8 = 5 → (redMat p M₂) ^ (p + 1) = 1) := by
  have hne : (2 : ZMod p) ≠ 0 := BerggrenSpectral.two_ne_zero_of_odd_prime p hp
  have hhalf : p / 2 = (p - 1) / 2 := by
    have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
    obtain ⟨t, ht⟩ := hodd; omega
  constructor
  · intro h8
    have hsq : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff hp).mpr h8
    have := (ZMod.euler_criterion p hne).mp hsq
    rw [hhalf] at this
    exact BerggrenSpectral.berg_two_resonance_qr p hp this
  · intro h8
    have hsq : ¬ IsSquare (2 : ZMod p) := by
      intro hs
      rcases (ZMod.exists_sq_eq_two_iff hp).mp hs with h | h <;> omega
    have hne1 : (2 : ZMod p) ^ ((p - 1) / 2) ≠ 1 := by
      intro hcon
      exact hsq ((ZMod.euler_criterion p hne).mpr (by rw [hhalf]; exact hcon))
    rcases BerggrenSpectral.two_chi_cases p hp with h | h
    · exact absurd h hne1
    · exact BerggrenSpectral.berg_two_resonance_nqr p hp h

end

end BerggrenSpectral

namespace BerggrenSpectral

theorem redMat_eq_one_iff (N : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) :
    redMat N A = 1 ↔ ∀ i j, (N : ℤ) ∣ (A - 1) i j := by
  have hmap : redMat N (A - 1) = redMat N A - 1 := by
    simp [redMat, map_sub]
  constructor
  · intro h i j
    have h0 : redMat N (A - 1) = 0 := by rw [hmap, h, sub_self]
    have h2 := congrFun (congrFun h0 i) j
    rw [BerggrenSpectral.redMat_apply] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by simpa using h2)
  · intro h
    have h0 : redMat N (A - 1) = 0 := by
      ext i j
      rw [BerggrenSpectral.redMat_apply]
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((A - 1) i j) N).mpr (h i j)
    rw [hmap] at h0
    exact sub_eq_zero.mp h0

end BerggrenSpectral

namespace BerggrenSpectral

theorem factor_extraction (p q : ℕ) (hq : q.Prime) (x : ℤ)
    (hpx : (p : ℤ) ∣ x) (hqx : ¬ (q : ℤ) ∣ x) (hp0 : p ≠ 0) :
    Int.gcd x ((p * q : ℕ) : ℤ) = p := by
  set g := Int.gcd x ((p * q : ℕ) : ℤ) with hg
  have hgx : (g : ℤ) ∣ x := Int.gcd_dvd_left _ _
  have hgN : g ∣ p * q := by exact_mod_cast Int.gcd_dvd_right x ((p * q : ℕ) : ℤ)
  have hpg : p ∣ g := by
    have h2 : (p : ℤ) ∣ ((p * q : ℕ) : ℤ) := by push_cast; exact Dvd.intro q rfl
    exact Int.dvd_gcd hpx h2
  obtain ⟨t, ht⟩ := hpg
  have htq : t ∣ q := (mul_dvd_mul_iff_left hp0).mp (ht ▸ hgN)
  rcases hq.eq_one_or_self_of_dvd t htq with h1 | h1
  · rw [ht, h1, mul_one]
  · exact absurd (((show (q : ℤ) ∣ (g : ℤ) by rw [ht, h1]; exact ⟨(p : ℤ), by push_cast; ring⟩)).trans
      hgx) hqx

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_resonance_extracts_factor (p q k : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hres : (redMat p M₂) ^ k = 1) (hnon : (redMat q M₂) ^ k ≠ 1) :
    ∃ i j, Int.gcd ((M₂ ^ k - 1) i j) ((p * q : ℕ) : ℤ) = p := by
  have hpdvd : ∀ i j, (p : ℤ) ∣ (M₂ ^ k - 1) i j := by
    refine (redMat_eq_one_iff p (M₂ ^ k)).mp ?_
    rw [BerggrenSpectral.redMat_pow]; exact hres
  have hqex : ∃ i j, ¬ (q : ℤ) ∣ (M₂ ^ k - 1) i j := by
    by_contra hcon
    push_neg at hcon
    exact hnon (by rw [← BerggrenSpectral.redMat_pow]; exact (redMat_eq_one_iff q (M₂ ^ k)).mpr hcon)
  obtain ⟨i, j, hij⟩ := hqex
  exact ⟨i, j, BerggrenSpectral.factor_extraction p q hq _ (hpdvd i j) hij hp.pos.ne'⟩

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_resonance_nontrivial (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    1 < p ∧ p < p * q ∧ p ∣ p * q := by
  refine ⟨hp.one_lt, ?_, Dvd.intro q rfl⟩
  have : 1 < q := hq.one_lt
  have hppos : 0 < p := hp.pos
  nlinarith [hppos, this]

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_resonance_factorization (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hnon : (redMat q M₂) ^ (p ^ 2 - 1) ≠ 1) :
    ∃ i j : Fin 3,
      Int.gcd ((M₂ ^ (p ^ 2 - 1) - 1 : Matrix (Fin 3) (Fin 3) ℤ) i j)
        ((p * q : ℕ) : ℤ) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact berg_resonance_extracts_factor p q _ hp hq (BerggrenSpectral.berg_two_resonance p hp2) hnon

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_resonance_sharp_frequency (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) :
    ((p % 8 = 1 ∨ p % 8 = 7) → (redMat q M₂) ^ (p - 1) ≠ 1 →
      ∃ i j, Int.gcd ((M₂ ^ (p - 1) - 1) i j) ((p * q : ℕ) : ℤ) = p) ∧
    ((p % 8 = 3 ∨ p % 8 = 5) → (redMat q M₂) ^ (p + 1) ≠ 1 →
      ∃ i j, Int.gcd ((M₂ ^ (p + 1) - 1) i j) ((p * q : ℕ) : ℤ) = p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := BerggrenSpectral.berg_two_resonance_mod_eight p hp2
  exact ⟨fun h8 hnon => berg_resonance_extracts_factor p q _ hp hq (h1 h8) hnon,
    fun h8 hnon => berg_resonance_extracts_factor p q _ hp hq (h2 h8) hnon⟩

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_aligned_resonance_no_factor (N k : ℕ) (h : (redMat N M₂) ^ k = 1) (i j : Fin 3) :
    Int.gcd ((M₂ ^ k - 1 : Matrix (Fin 3) (Fin 3) ℤ) i j) (N : ℤ) = N := by
  have hdvd : (N : ℤ) ∣ (M₂ ^ k - 1) i j := by
    refine (redMat_eq_one_iff N (M₂ ^ k)).mp ?_ i j
    rw [BerggrenSpectral.redMat_pow]; exact h
  refine Nat.dvd_antisymm ?_ ?_
  · exact_mod_cast Int.gcd_dvd_right ((M₂ ^ k - 1) i j) (N : ℤ)
  · exact Int.dvd_gcd hdvd dvd_rfl

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_resonance_three : (redMat 3 M₂) ^ 4 = 1 := by decide

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_no_resonance_five : (redMat 5 M₂) ^ 4 ≠ 1 := by decide

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_factor_fifteen :
    ∃ i j : Fin 3,
      Int.gcd ((M₂ ^ 4 - 1 : Matrix (Fin 3) (Fin 3) ℤ) i j) ((3 * 5 : ℕ) : ℤ) = 3 :=
  berg_resonance_extracts_factor 3 5 4 (by norm_num) (by norm_num)
    berg_resonance_three BerggrenSpectral.berg_no_resonance_five

end BerggrenSpectral

namespace BerggrenSpectral

set_option maxRecDepth 40000 in
/-- `53 ≡ 5 (mod 8)`, so the resonant frequency of `p = 53` divides `53 + 1 = 54`. -/
theorem berg_resonance_53 : (redMat 53 M₂) ^ 54 = 1 := by decide

end BerggrenSpectral

namespace BerggrenSpectral

set_option maxRecDepth 40000 in
/-- `61` is out of resonance at frequency `54` (its own frequency is `62`). -/
theorem berg_no_resonance_61 : (redMat 61 M₂) ^ 54 ≠ 1 := by decide

end BerggrenSpectral

namespace BerggrenSpectral

theorem berg_factor_3233 :
    ∃ i j : Fin 3,
      Int.gcd ((M₂ ^ 54 - 1 : Matrix (Fin 3) (Fin 3) ℤ) i j) ((53 * 61 : ℕ) : ℤ) = 53 :=
  berg_resonance_extracts_factor 53 61 54 (by norm_num) (by norm_num)
    berg_resonance_53 BerggrenSpectral.berg_no_resonance_61

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_two_pow_eq_one_iff (hp : p ≠ 2) (k : ℕ) :
    (redMat p M₂) ^ k = 1 ↔ (bergU (ZMod p)) ^ k = 1 ∧ Even k := by
  rw [BerggrenSpectral.redMat_M₂]
  constructor
  · intro h
    have hdet : IsUnit (bergW (ZMod p)).det := by
      rw [BerggrenSpectral.det_bergW]; exact (isUnit_iff_ne_zero).mpr (BerggrenSpectral.two_ne_zero_of_odd_prime p hp)
    haveI : Invertible (bergW (ZMod p)) := invertibleOfIsUnitDet _ hdet
    have hc := BerggrenSpectral.berg_pow_conj (R := ZMod p) k
    rw [h, one_mul] at hc
    have hV : (bergV (ZMod p)) ^ k = 1 := by
      have hW : bergW (ZMod p) * (bergV (ZMod p)) ^ k = bergW (ZMod p) * 1 := by
        rw [mul_one, ← hc]
      exact mul_right_injective_of_invertible (bergW (ZMod p)) hW
    rw [BerggrenSpectral.bergV_pow] at hV
    have h00 := congrFun (congrFun hV 0) 0
    have h01 := congrFun (congrFun hV 0) 1
    have h10 := congrFun (congrFun hV 1) 0
    have h11 := congrFun (congrFun hV 1) 1
    have h22 := congrFun (congrFun hV 2) 2
    simp [blockEmbed] at h00 h01 h10 h11 h22
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp <;> assumption
    · rcases Nat.even_or_odd k with he | ho
      · exact he
      · exfalso
        rw [ho.neg_one_pow] at h22
        exact BerggrenSpectral.two_ne_zero_of_odd_prime p hp (by linear_combination -h22)
  · rintro ⟨hU, hk⟩
    exact BerggrenSpectral.M2R_pow_eq_one p hp hU hk

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_two_orderOf (hp : p ≠ 2) :
    orderOf (redMat p M₂) = Nat.lcm 2 (orderOf (bergU (ZMod p))) := by
  set d := orderOf (bergU (ZMod p)) with hd
  refine Nat.dvd_antisymm ?_ ?_
  · refine orderOf_dvd_of_pow_eq_one ((BerggrenSpectral.berg_two_pow_eq_one_iff p hp _).mpr ⟨?_, ?_⟩)
    · exact orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right 2 d)
    · exact (even_iff_exists_two_nsmul _).mpr (Nat.dvd_lcm_left 2 d)
  · obtain ⟨hU, hk⟩ :=
      (BerggrenSpectral.berg_two_pow_eq_one_iff p hp (orderOf (redMat p M₂))).mp (pow_orderOf_eq_one _)
    exact Nat.lcm_dvd hk.two_dvd (orderOf_dvd_of_pow_eq_one hU)

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_resonance_crt (m n k : ℕ) (h : Nat.Coprime m n) :
    (redMat (m * n) M₂) ^ k = 1 ↔ (redMat m M₂) ^ k = 1 ∧ (redMat n M₂) ^ k = 1 := by
  have hco : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  rw [← BerggrenSpectral.redMat_pow, ← BerggrenSpectral.redMat_pow, ← BerggrenSpectral.redMat_pow, redMat_eq_one_iff, redMat_eq_one_iff,
    redMat_eq_one_iff]
  constructor
  · intro hall
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact dvd_trans ⟨(n : ℤ), by push_cast; ring⟩ (hall i j)
    · exact dvd_trans ⟨(m : ℤ), by push_cast; ring⟩ (hall i j)
  · rintro ⟨h1, h2⟩ i j
    have := hco.mul_dvd (h1 i j) (h2 i j)
    simpa [Nat.cast_mul] using this

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_two_cayley : M₂ ^ 3 = (5 : ℤ) • M₂ ^ 2 + (5 : ℤ) • M₂ - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M₂, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_trace_values :
    bergTrace 0 = 3 ∧ bergTrace 1 = 5 ∧ bergTrace 2 = 35 ∧ bergTrace 3 = 197 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bergTrace, M₂, pow_succ, Matrix.trace_fin_three]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_trace_rec (k : ℕ) :
    bergTrace (k + 3) = 5 * bergTrace (k + 2) + 5 * bergTrace (k + 1) - bergTrace k := by
  have h : M₂ ^ (k + 3) = M₂ ^ k * ((5 : ℤ) • M₂ ^ 2 + (5 : ℤ) • M₂ - 1) := by
    rw [← BerggrenSpectral.berg_two_cayley, ← pow_add]
  have expand : M₂ ^ k * ((5 : ℤ) • M₂ ^ 2 + (5 : ℤ) • M₂ - 1)
      = (5 : ℤ) • M₂ ^ (k + 2) + (5 : ℤ) • M₂ ^ (k + 1) - M₂ ^ k := by
    rw [mul_sub, mul_add, mul_smul_comm, mul_smul_comm, mul_one, ← pow_add, ← pow_succ]
  show Matrix.trace (M₂ ^ (k + 3)) = _
  rw [h, expand, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    smul_eq_mul, smul_eq_mul]
  rfl

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem bergTrace_cast (m k : ℕ) :
    ((bergTrace k : ℤ) : ZMod m) = Matrix.trace ((M2R (ZMod m)) ^ k) := by
  rw [← BerggrenSpectral.redMat_M₂, ← BerggrenSpectral.redMat_pow]
  simp [bergTrace, Matrix.trace_fin_three, BerggrenSpectral.redMat_apply]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem trace_M2R_pow (hp : p ≠ 2) (k : ℕ) :
    Matrix.trace ((M2R (ZMod p)) ^ k)
      = Matrix.trace ((bergU (ZMod p)) ^ k) + (-1 : ZMod p) ^ k := by
  have hdet : IsUnit (bergW (ZMod p)).det := by
    rw [BerggrenSpectral.det_bergW]; exact (isUnit_iff_ne_zero).mpr (BerggrenSpectral.two_ne_zero_of_odd_prime p hp)
  haveI : Invertible (bergW (ZMod p)) := invertibleOfIsUnitDet _ hdet
  have hc := BerggrenSpectral.berg_pow_conj (R := ZMod p) k
  have hinv : (bergW (ZMod p))⁻¹ * bergW (ZMod p) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hM : (M2R (ZMod p)) ^ k = bergW (ZMod p) * (bergV (ZMod p)) ^ k * (bergW (ZMod p))⁻¹ := by
    rw [← hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
  rw [hM, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hinv, mul_one, BerggrenSpectral.bergV_pow]
  simp [blockEmbed, Matrix.trace_fin_three, Matrix.trace_fin_two]

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_trace_fermat (hp : p ≠ 2) : ((bergTrace p : ℤ) : ZMod p) = 5 := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  have hU : Matrix.trace ((bergU (ZMod p)) ^ p) = 6 := by
    rw [BerggrenSpectral.bergU_frob p hp]
    simp [bergS, Matrix.trace_fin_two]
    ring
  rw [BerggrenSpectral.bergTrace_cast, BerggrenSpectral.trace_M2R_pow p hp, hU, hodd.neg_one_pow]
  ring

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_trace_fermat_int (hp : p ≠ 2) : (p : ℤ) ∣ bergTrace p - 5 := by
  have h := BerggrenSpectral.berg_trace_fermat p hp
  have : ((bergTrace p - 5 : ℤ) : ZMod p) = 0 := by push_cast [h]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_trace_composite_witness (N : ℕ) (hN : N ≠ 2) (h : ¬ ((N : ℤ) ∣ bergTrace N - 5)) :
    ¬ N.Prime := by
  intro hprime
  haveI : Fact N.Prime := ⟨hprime⟩
  exact h (BerggrenSpectral.berg_trace_fermat_int N hN)

end

end BerggrenSpectral

namespace BerggrenSpectral

section
variable (p : ℕ) [Fact p.Prime]

theorem berg_nine_composite_witness : ¬ (9 : ℕ).Prime := by
  refine BerggrenSpectral.berg_trace_composite_witness 9 (by norm_num) ?_
  have h9 : bergTrace 9 = 7761797 := by
    simp [bergTrace, M₂, pow_succ, Matrix.trace_fin_three]
  rw [h9]
  decide

end

end BerggrenSpectral


theorem solution (hp : p ≠ 2) (k : ℕ) :
    (redMat p M₂) ^ k = 1 ↔ (bergU (ZMod p)) ^ k = 1 ∧ Even k := by
  rw [BerggrenSpectral.redMat_M₂]
  constructor
  · intro h
    have hdet : IsUnit (bergW (ZMod p)).det := by
      rw [BerggrenSpectral.det_bergW]; exact (isUnit_iff_ne_zero).mpr (BerggrenSpectral.two_ne_zero_of_odd_prime p hp)
    haveI : Invertible (bergW (ZMod p)) := invertibleOfIsUnitDet _ hdet
    have hc := BerggrenSpectral.berg_pow_conj (R := ZMod p) k
    rw [h, one_mul] at hc
    have hV : (bergV (ZMod p)) ^ k = 1 := by
      have hW : bergW (ZMod p) * (bergV (ZMod p)) ^ k = bergW (ZMod p) * 1 := by
        rw [mul_one, ← hc]
      exact mul_right_injective_of_invertible (bergW (ZMod p)) hW
    rw [BerggrenSpectral.bergV_pow] at hV
    have h00 := congrFun (congrFun hV 0) 0
    have h01 := congrFun (congrFun hV 0) 1
    have h10 := congrFun (congrFun hV 1) 0
    have h11 := congrFun (congrFun hV 1) 1
    have h22 := congrFun (congrFun hV 2) 2
    simp [blockEmbed] at h00 h01 h10 h11 h22
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp <;> assumption
    · rcases Nat.even_or_odd k with he | ho
      · exact he
      · exfalso
        rw [ho.neg_one_pow] at h22
        exact BerggrenSpectral.two_ne_zero_of_odd_prime p hp (by linear_combination -h22)
  · rintro ⟨hU, hk⟩
    exact BerggrenSpectral.M2R_pow_eq_one p hp hU hk

#print axioms solution
