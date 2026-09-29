-- Prove2me | solution 1 for PadicBerggren.B2_not_transitive_on_nullCone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T23:26:04.977574+00:00
-- url     : https://prove2.me/submissions/a8bf857b-73b4-4fe8-bde5-8b49d54ee6bb

-- Thm stub generated from Geometry/PadicBerggrenOrbits.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Definitions.Def_Geometry_PadicBerggrenNullCone
import Theorems.Thm_PadicBerggren_B2_pow_eq_one_of_block
import Theorems.Thm_PadicBerggren_B2_pow_p_add_one_of_not_isSquare_two
import Theorems.Thm_PadicBerggren_B2_pow_p_sub_one_of_isSquare_two

/-!
# Orbit structure of the reduced Berggren dynamics

Building on `Catalog/Geometry/PadicBerggrenDynamics.lean` (the three Berggren generators as a
dynamical system on `(ZMod (p^k))³`) and on `Catalog/Geometry/PadicBerggrenNullCone.lean`
(the phase space has exactly `p²` points), this file settles the **orbit structure** of the
generators on the null cone mod an odd prime.

## Main results

* `PadicBerggren.pow_mod_eq` : an elementary periodicity reduction, `M^n = M^(n % m)` whenever
  `M^m = 1`.
* `PadicBerggren.B₂_pow_le_p_add_one` : for every odd prime there is a period `m` with
  `1 ≤ m ≤ p + 1` and `B₂^m = 1` — either `p − 1` (split case, `2` a square mod `p`) or
  `p + 1` (inert case).  So the *actual* period of the hyperbolic generator is at most `p + 1`,
  much smaller than the a priori bound `p² − 1`.
* `PadicBerggren.B₂_orbit_card_le` : every `B₂`-orbit on `(ZMod p)³` has at most `p + 1` points.
* `PadicBerggren.B₂_not_transitive_on_nullCone` : consequently, for every odd prime the
  hyperbolic generator is **never transitive** on the `p² − 1` nonzero null vectors: the reduced
  Berggren dynamics is *never ergodic* on the null cone, and there are at least
  `(p² − 1)/(p + 1) = p − 1` distinct orbits.  This is the precise sense in which the p-adic
  picture differs from the real one, where the hyperbolic generator has dense orbits on the
  boundary.
* `PadicBerggren.card_B1_fixedPoints` : the unipotent generator fixes exactly `p` points — a
  whole isotropic line — whereas `B₂` fixes only the origin (`B₂_no_nonzero_fixed_point`).
  This is the counting form of the unipotent/hyperbolic spectral dichotomy.
-/

open PadicBerggren

open Matrix Finset


variable (p : ℕ) [Fact p.Prime]

variable {R : Type*} [CommRing R]
theorem B₂_pow_le_p_add_one (hp : p ≠ 2) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ p + 1 ∧ (B₂ (ZMod p)) ^ m = 1 := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have h2 := hpp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp
    · exact h
  by_cases h : IsSquare (2 : ZMod p)
  · exact ⟨p - 1, by omega, by omega, B2_pow_p_sub_one_of_isSquare_two p hp h⟩
  · exact ⟨p + 1, by omega, le_rfl, B2_pow_p_add_one_of_not_isSquare_two p hp h⟩

theorem pow_mod_eq {M : Type*} [Monoid M] (x : M) (m : ℕ) (hm : x ^ m = 1) (n : ℕ) :
    x ^ n = x ^ (n % m) := by
  conv_lhs => rw [← Nat.div_add_mod n m]
  rw [pow_add, pow_mul, hm, one_pow, one_mul]

theorem B₂_orbit_card_le (hp : p ≠ 2) (v : Fin 3 → ZMod p) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ p + 1 ∧
      ∀ n : ℕ, ∃ r < m, (B₂ (ZMod p)) ^ n *ᵥ v = (B₂ (ZMod p)) ^ r *ᵥ v := by
  obtain ⟨m, hm1, hm2, hm⟩ := B₂_pow_le_p_add_one p hp
  refine ⟨m, hm1, hm2, fun n => ⟨n % m, Nat.mod_lt _ (by omega), ?_⟩⟩
  rw [pow_mod_eq (B₂ (ZMod p)) m hm n]

theorem zero_mem_nullConeFinset : (0 : Fin 3 → ZMod p) ∈ nullConeFinset p := by
  simp [nullConeFinset, lorentz]

theorem two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

theorem eta3 (w : Fin 3 → ZMod p) : w = ![w 0, w 1, w 2] := by
  funext i; fin_cases i <;> rfl

theorem card_nullCone_fiber (hp : p ≠ 2) (u : ZMod p) :
    ((nullConeFinset p).filter (fun w => w 2 - w 0 = u)).card = p := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp
  rcases eq_or_ne u 0 with rfl | hu
  · have hinj : Function.Injective (fun s : ZMod p => (![s, 0, s] : Fin 3 → ZMod p)) := by
      intro a b hab
      have := congrFun hab 0
      simpa using this
    have himg : ((nullConeFinset p).filter (fun w => w 2 - w 0 = 0))
        = image (fun s : ZMod p => (![s, 0, s] : Fin 3 → ZMod p)) univ := by
      ext w
      simp only [mem_filter, mem_image, mem_univ, true_and, nullConeFinset, lorentz]
      constructor
      · rintro ⟨hq, hd⟩
        have hw2 : w 2 = w 0 := by linear_combination hd
        have hw1 : w 1 = 0 := by
          have hsq : (w 1) ^ 2 = 0 := by rw [hw2] at hq; linear_combination hq
          exact sq_eq_zero_iff.mp hsq
        refine ⟨w 0, ?_⟩
        funext i
        fin_cases i <;> simp [hw1, hw2]
      · rintro ⟨s, rfl⟩
        refine ⟨?_, ?_⟩ <;> simp
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  · have hui : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
    have hc : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
    have hinj : Function.Injective (fun b : ZMod p =>
        (![(b ^ 2 * u⁻¹ - u) * (2 : ZMod p)⁻¹, b, (b ^ 2 * u⁻¹ + u) * (2 : ZMod p)⁻¹] :
          Fin 3 → ZMod p)) := by
      intro a b hab
      have := congrFun hab 1
      simpa using this
    have himg : ((nullConeFinset p).filter (fun w => w 2 - w 0 = u))
        = image (fun b : ZMod p =>
            (![(b ^ 2 * u⁻¹ - u) * (2 : ZMod p)⁻¹, b, (b ^ 2 * u⁻¹ + u) * (2 : ZMod p)⁻¹] :
              Fin 3 → ZMod p)) univ := by
      ext w
      simp only [mem_filter, mem_image, mem_univ, true_and, nullConeFinset, lorentz]
      constructor
      · rintro ⟨hq, hd⟩
        refine ⟨w 1, ?_⟩
        have hsum : u * (w 2 + w 0) = (w 1) ^ 2 := by
          have hw2 : w 2 = u + w 0 := by linear_combination hd
          rw [hw2] at hq ⊢
          linear_combination -hq
        have hs : w 2 + w 0 = (w 1) ^ 2 * u⁻¹ := by
          field_simp
          linear_combination hsum
        have hA : ((w 1) ^ 2 * u⁻¹ - u) * (2 : ZMod p)⁻¹ = w 0 := by
          linear_combination (-(2 : ZMod p)⁻¹) * hs + (2 : ZMod p)⁻¹ * hd + w 0 * hc
        have hC : ((w 1) ^ 2 * u⁻¹ + u) * (2 : ZMod p)⁻¹ = w 2 := by
          linear_combination (-(2 : ZMod p)⁻¹) * hs + (-(2 : ZMod p)⁻¹) * hd + w 2 * hc
        rw [hA, hC, ← eta3 p w]
      · rintro ⟨b, rfl⟩
        refine ⟨?_, ?_⟩
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          linear_combination (-4 * ((2 : ZMod p)⁻¹) ^ 2 * b ^ 2) * hui +
            (-(b ^ 2 * (2 * (2 : ZMod p)⁻¹ + 1))) * hc
        · simp only [Matrix.cons_val_zero, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          linear_combination u * hc
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

theorem card_nullCone (hp : p ≠ 2) : (nullConeFinset p).card = p ^ 2 := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun w : Fin 3 → ZMod p => w 2 - w 0) (s := nullConeFinset p)
    (t := (univ : Finset (ZMod p))) (fun x _ => mem_univ _)
  rw [hfib, Finset.sum_congr rfl (fun u _ => card_nullCone_fiber p hp u),
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, sq]

theorem card_nullCone_nonzero (hp : p ≠ 2) :
    ((nullConeFinset p).erase 0).card = p ^ 2 - 1 := by
  rw [Finset.card_erase_of_mem (zero_mem_nullConeFinset p), card_nullCone p hp]

theorem B₂_pow_card_sq_sub_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (B₂ (ZMod p)) ^ (p ^ 2 - 1) = 1 := by
  have hpp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hpp.one_lt.le.trans' (by omega)
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have := Nat.sq_sub_sq p 1
    simpa using this
  by_cases h : IsSquare (2 : ZMod p)
  · rw [hfac, mul_comm, pow_mul, B2_pow_p_sub_one_of_isSquare_two p hp h, one_pow]
  · rw [hfac, pow_mul, B2_pow_p_add_one_of_not_isSquare_two p hp h, one_pow]

theorem scal2_commute (a : R) (M : Matrix (Fin 2) (Fin 2) R) : Commute (scal2 a) M := by
  unfold Commute SemiconjBy scal2
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

theorem scal2_eq (c : R) : scal2 c = !![c, 0; 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scal2]

theorem scal2_mul (a b : R) : scal2 a * scal2 b = scal2 (a * b) := by
  simp only [scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem scal2_pow (a : R) (n : ℕ) : (scal2 a) ^ n = scal2 (a ^ n) := by
  induction n with
  | zero => simp [scal2]
  | succ n ih => rw [pow_succ, ih, scal2_mul, pow_succ]

theorem Jm_sq : (Jm R) ^ 2 = scal2 (2 : R) := by
  rw [pow_two]
  simp only [scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Jm_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Jm (ZMod p)) ^ p = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hpp : p.Prime := Fact.out
  have h2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have hp' : p = 2 * (p / 2) + 1 := by omega
  calc (Jm (ZMod p)) ^ p = ((Jm (ZMod p)) ^ 2) ^ (p / 2) * Jm (ZMod p) := by
        rw [← pow_mul, ← pow_succ]; exact congrArg _ hp'
    _ = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by rw [Jm_sq, scal2_pow]

theorem Um_decomp : Um R = scal2 (3 : R) + scal2 (2 : R) * Jm R := by
  simp only [scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Um, Jm]; try ring)

theorem Um_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Um (ZMod p)) ^ p
      = scal2 (3 : ZMod p) + scal2 (2 * (2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hcomm : Commute (scal2 (3 : ZMod p)) (scal2 (2 : ZMod p) * Jm (ZMod p)) :=
    scal2_commute _ _
  rw [Um_decomp, add_pow_char_of_commute p hcomm,
    Commute.mul_pow (scal2_commute (2 : ZMod p) (Jm (ZMod p))), scal2_pow, scal2_pow,
    Jm_pow_card p hp, ZMod.pow_card, ZMod.pow_card, ← mul_assoc, scal2_mul]

theorem Um_mul_inv : Um R * !![3, -2; -4, 3] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Um_conj_mul : (scal2 (3 : R) + scal2 (-2 : R) * Jm R) * Um R = 1 := by
  simp only [scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem two_pow_div_two_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ^ (p / 2) = 1 ∨ (2 : ZMod p) ^ (p / 2) = -1 := by
  have hpp : p.Prime := Fact.out
  have hmod : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have hsq : ((2 : ZMod p) ^ (p / 2)) * ((2 : ZMod p) ^ (p / 2)) = 1 := by
    rw [← pow_add]
    have : p / 2 + p / 2 = p - 1 := by omega
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one h2
  exact mul_self_eq_one_iff.mp hsq


open PadicBerggren in
theorem solution (hp : p ≠ 2) (v : Fin 3 → ZMod p) :
    ¬ (∀ w ∈ (nullConeFinset p).erase 0, ∃ n : ℕ, (B₂ (ZMod p)) ^ n *ᵥ v = w) := by
  intro htrans
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp
    · exact h
  obtain ⟨m, hm1, hm2, hred⟩ := B₂_orbit_card_le p hp v
  have hsub : (nullConeFinset p).erase 0 ⊆
      Finset.image (fun n : ℕ => (B₂ (ZMod p)) ^ n *ᵥ v) (Finset.range m) := by
    intro w hw
    obtain ⟨n, hn⟩ := htrans w hw
    obtain ⟨r, hr, hrn⟩ := hred n
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by rw [← hrn, hn]⟩
  have hcard : ((nullConeFinset p).erase 0).card ≤ m :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_image_le) (by simp))
  rw [card_nullCone_nonzero p hp] at hcard
  have hsq : p + 3 ≤ p ^ 2 := by nlinarith
  omega

/-! ### The split case: an explicit null eigenvector and its exact period

When `2` is a square mod `p` (equivalently `p ≡ ±1 mod 8`) the hyperbolic generator has the
null eigenvector `(1,1,√2)` with eigenvalue `3 + 2√2`, the fundamental unit squared.  Its orbit
is therefore the geometric progression of the eigenvalue, and its exact period is the
multiplicative order of `3 + 2√2` in `(ZMod p)ˣ`. -/
