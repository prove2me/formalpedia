-- Prove2me | solution 1 for BerggrenSpectral.berg_two_resonance_nqr
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:33.228759+00:00
-- url     : https://prove2.me/submissions/8cbf8fca-0ceb-4163-8300-a002708b0241

-- Thm stub generated from Cryptography/BerggrenSpectral/HyperbolicResonance.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance

/-!
# Hyperbolic Berggren Resonance: the frequencies `2(p ∓ 1)`

The middle Berggren generator `M₂` is hyperbolic, with spectrum `{-1, 3 + 2√2, 3 - 2√2}`
(`berg_charpoly_two`).  This file proves that **modulo a prime `p` the resonant exponent of
`M₂` is `2(p - 1)` or `2(p + 1)` according to the quadratic character of `2`, i.e. according
to `p mod 8`** — the "energy frequency" of the hyperbolic branch is locked to the prime.

The proof is a fully explicit Frobenius computation.

1.  `berg_conj`: the integral conjugation `M₂ * W = W * V`, where the columns of
    `W = !![1,0,1; 1,0,-1; 0,1,0]` are the invariant vectors `(1,1,0)`, `(0,0,1)` and the
    `-1`-eigenvector `(1,-1,0)`, and `V` is block diagonal with blocks `U = !![3,2;4,3]`
    and `(-1)`.
2.  `bergU_frob`: over `ZMod p`, `U = 3 + S` with `S² = 8`, so the Frobenius endomorphism
    gives `U ^ p = 3 + 8^((p-1)/2) • S`; this is the matrix incarnation of
    `(3 + 2√2)^p = 3 ± 2√2` in `𝔽_p(√2)`.
3.  Hence `U ^ (p - 1) = 1` when `2` is a square mod `p` and `U ^ (p + 1) = 1` otherwise
    (`bergU_pow_qr`, `bergU_pow_nqr`), because `U⁻¹ = 6 - U`.
4.  Transporting back through `W` (invertible because `det W = -2` and `p` is odd) and
    squaring to kill the `-1` eigenvalue yields the main theorems
    `berg_two_resonance_qr`, `berg_two_resonance_nqr`, `berg_two_resonance_mod_eight`
    and the uniform `berg_two_resonance` : `M₂ ^ (2 * (p² - 1)) ≡ 1 (mod p)`.

This is the exact analogue, for the Pythagorean/Berggren tree, of the Lucas–Lehmer and
Pollard `p ± 1` phenomena; the factoring consequences are in `Factorization.lean`.
-/

open BerggrenSpectral

open Matrix

variable (R : Type*) [CommRing R]

/-! ## The hyperbolic block and the conjugating matrix -/







variable {R}








/-! ## Algebraic identities for the hyperbolic block -/





/-! ## Frobenius over `ZMod p` -/

variable (p : ℕ) [Fact p.Prime]








/-! ## Transport back to `M₂` -/

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


theorem solution (hp : p ≠ 2) (h : (2 : ZMod p) ^ ((p - 1) / 2) = -1) :
    (redMat p M₂) ^ (p + 1) = 1 := by
  rw [BerggrenSpectral.redMat_M₂]
  exact BerggrenSpectral.M2R_pow_eq_one p hp (BerggrenSpectral.bergU_pow_nqr p hp h) (BerggrenSpectral.even_add_one p hp)

#print axioms solution
