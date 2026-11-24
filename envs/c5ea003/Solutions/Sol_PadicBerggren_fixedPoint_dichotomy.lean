-- Prove2me | solution 1 for PadicBerggren.fixedPoint_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:03:49.41345+00:00
-- url     : https://prove2.me/submissions/d5486890-b09f-406d-a5cc-9c21a8134033

-- Thm stub generated from Geometry/PadicBerggrenOrbits.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Definitions.Def_Geometry_PadicBerggrenNullCone

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
* `PadicBerggren.card_B₁_fixedPoints` : the unipotent generator fixes exactly `p` points — a
  whole isotropic line — whereas `B₂` fixes only the origin (`B₂_no_nonzero_fixed_point`).
  This is the counting form of the unipotent/hyperbolic spectral dichotomy.
-/

open PadicBerggren

open Matrix Finset


variable (p : ℕ) [Fact p.Prime]




/-! ### The split case: an explicit null eigenvector and its exact period

When `2` is a square mod `p` (equivalently `p ≡ ±1 mod 8`) the hyperbolic generator has the
null eigenvector `(1,1,√2)` with eigenvalue `3 + 2√2`, the fundamental unit squared.  Its orbit
is therefore the geometric progression of the eigenvalue, and its exact period is the
multiplicative order of `3 + 2√2` in `(ZMod p)ˣ`. -/

open Matrix
open Matrix Finset
namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₁ (v : Fin 3 → R) : lorentz R (B₁ R *ᵥ v) = lorentz R v := by
  simp [lorentz, B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₂ (v : Fin 3 → R) : lorentz R (B₂ R *ᵥ v) = lorentz R v := by
  simp [lorentz, B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₃ (v : Fin 3 → R) : lorentz R (B₃ R *ᵥ v) = lorentz R v := by
  simp [lorentz, B₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_C₁ (v : Fin 3 → R) : lorentz R (C₁ R *ᵥ v) = lorentz R v := by
  simp [lorentz, C₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_C₂ (v : Fin 3 → R) : lorentz R (C₂ R *ᵥ v) = lorentz R v := by
  simp [lorentz, C₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_C₃ (v : Fin 3 → R) : lorentz R (C₃ R *ᵥ v) = lorentz R v := by
  simp [lorentz, C₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem det_B₁ : (B₁ R).det = 1 := by simp [B₁, Matrix.det_fin_three]; ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem det_B₂ : (B₂ R).det = -1 := by simp [B₂, Matrix.det_fin_three]; ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem det_B₃ : (B₃ R).det = 1 := by simp [B₃, Matrix.det_fin_three]; ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_mul_C₁ : B₁ R * C₁ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₁, C₁, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem C₁_mul_B₁ : C₁ R * B₁ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₁, C₁, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_mul_C₂ : B₂ R * C₂ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₂, C₂, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem C₂_mul_B₂ : C₂ R * B₂ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₂, C₂, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_mul_C₃ : B₃ R * C₃ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₃, C₃, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem C₃_mul_B₃ : C₃ R * B₃ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₃, C₃, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_of_inverse (M N : Matrix (Fin 3) (Fin 3) R) (hMN : M * N = 1) (hNM : N * M = 1)
    (hM : ∀ v, lorentz R (M *ᵥ v) = lorentz R v)
    (hN : ∀ v, lorentz R (N *ᵥ v) = lorentz R v) :
    Set.BijOn (fun v => M *ᵥ v) (nullCone R) (nullCone R) := by
  refine ⟨fun v hv => ?_, fun v _ w _ h => ?_, fun w hw => ⟨N *ᵥ w, ?_, ?_⟩⟩
  · simpa [nullCone, Set.mem_setOf_eq, hM v] using hv
  · have := congrArg (fun u => N *ᵥ u) h
    simpa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using this
  · simpa [nullCone, Set.mem_setOf_eq, hN w] using hw
  · simp [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_nullCone_B₁ : Set.BijOn (fun v => B₁ R *ᵥ v) (nullCone R) (nullCone R) :=
  bijOn_of_inverse _ _ PadicBerggren.B₁_mul_C₁ PadicBerggren.C₁_mul_B₁ PadicBerggren.lorentz_B₁ PadicBerggren.lorentz_C₁

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_nullCone_B₂ : Set.BijOn (fun v => B₂ R *ᵥ v) (nullCone R) (nullCone R) :=
  bijOn_of_inverse _ _ PadicBerggren.B₂_mul_C₂ PadicBerggren.C₂_mul_B₂ PadicBerggren.lorentz_B₂ PadicBerggren.lorentz_C₂

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_nullCone_B₃ : Set.BijOn (fun v => B₃ R *ᵥ v) (nullCone R) (nullCone R) :=
  bijOn_of_inverse _ _ PadicBerggren.B₃_mul_C₃ PadicBerggren.C₃_mul_B₃ PadicBerggren.lorentz_B₃ PadicBerggren.lorentz_C₃

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_eq_one_add : B₁ R = 1 + N₁ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₁, N₁] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_eq_one_add : B₃ R = 1 + N₃ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₃, N₃] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_sq : (N₁ R) ^ 2 = !![0, 0, 0; 0, -4, 4; 0, -4, 4] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₁, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_cube : (N₁ R) ^ 3 = 0 := by
  rw [pow_succ, PadicBerggren.N₁_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₁, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₃_sq : (N₃ R) ^ 2 = !![-4, 0, 4; 0, 0, 0; -4, 0, 4] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₃, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₃_cube : (N₃ R) ^ 3 = 0 := by
  rw [pow_succ, PadicBerggren.N₃_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₃, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_sq_ne_zero (h4 : (4 : R) ≠ 0) : (N₁ R) ^ 2 ≠ 0 := by
  intro h
  rw [PadicBerggren.N₁_sq] at h
  have := congrFun (congrFun h 1) 2
  simp at this
  exact h4 (by linear_combination this)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_sq_eq_zero_of_four_eq_zero (h4 : (4 : R) = 0) : (N₁ R) ^ 2 = 0 := by
  rw [PadicBerggren.N₁_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h4]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem pow_unipotent_formula {S : Type*} [Ring S] (X : S) (hX : X ^ 3 = 0) (n : ℕ) :
    (1 + X) ^ n = 1 + (n : S) * X + ((n.choose 2 : ℕ) : S) * X ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hc : (((n + 1).choose 2 : ℕ) : S) = ((n.choose 2 : ℕ) : S) + (n : S) := by
        rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
        push_cast
        exact add_comm _ _
      have expand : (1 + (n : S) * X + ((n.choose 2 : ℕ) : S) * X ^ 2) * (1 + X)
          = (1 + ((n : S) + 1) * X + (((n.choose 2 : ℕ) : S) + (n : S)) * X ^ 2)
            + ((n.choose 2 : ℕ) : S) * X ^ 3 := by
        noncomm_ring
      rw [pow_succ, ih, expand, hX, mul_zero, add_zero]
      push_cast [hc]
      noncomm_ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem natCast_matrix_mul {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ)
    (M : Matrix n n R) : ((m : Matrix n n R)) * M = (m : R) • M := by
  have h : ((m : ℕ) : Matrix n n R) = (m : R) • (1 : Matrix n n R) := by
    ext i j
    simp [Matrix.natCast_apply, Matrix.one_apply, apply_ite ((↑) : ℕ → R)]
  rw [h, Matrix.smul_mul, one_mul]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem pow_dvd_choose_two (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ^ k ∣ (p ^ k).choose 2 := by
  have h2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left hodd
  have hodd' : p ^ k % 2 = 1 := by simp [Nat.pow_mod, h2]
  obtain ⟨t, ht⟩ : ∃ t, p ^ k = 2 * t + 1 := ⟨p ^ k / 2, by omega⟩
  refine ⟨t, ?_⟩
  have h1 : 2 * t + 1 - 1 = 2 * t := by omega
  have key : (2 * t + 1) * (2 * t) = ((2 * t + 1) * t) * 2 := by ring
  rw [Nat.choose_two_right, ht, h1, key]
  generalize (2 * t + 1) * t = A
  omega

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem choose_two_cast_eq_zero (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (((p ^ k).choose 2 : ℕ) : ZMod (p ^ k)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact PadicBerggren.pow_dvd_choose_two p k hp hodd

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_pow_p_pow (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (B₁ (ZMod (p ^ k))) ^ (p ^ k) = 1 := by
  have hpk : ((p ^ k : ℕ) : ZMod (p ^ k)) = 0 := ZMod.natCast_self _
  have hchoose := PadicBerggren.choose_two_cast_eq_zero p k hp hodd
  rw [PadicBerggren.B₁_eq_one_add, PadicBerggren.pow_unipotent_formula _ PadicBerggren.N₁_cube]
  rw [natCast_matrix_eq_zero _ hpk, natCast_matrix_eq_zero _ hchoose]
  simp

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_pow_p_pow (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (B₃ (ZMod (p ^ k))) ^ (p ^ k) = 1 := by
  have hpk : ((p ^ k : ℕ) : ZMod (p ^ k)) = 0 := ZMod.natCast_self _
  have hchoose := PadicBerggren.choose_two_cast_eq_zero p k hp hodd
  rw [PadicBerggren.B₃_eq_one_add, PadicBerggren.pow_unipotent_formula _ PadicBerggren.N₃_cube]
  rw [natCast_matrix_eq_zero _ hpk, natCast_matrix_eq_zero _ hchoose]
  simp

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_order_exact (p k m : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (h : (B₁ (ZMod (p ^ k))) ^ m = 1) : p ^ k ∣ m := by
  rw [PadicBerggren.B₁_eq_one_add, PadicBerggren.pow_unipotent_formula _ PadicBerggren.N₁_cube] at h
  have h01 := congrFun (congrFun h 0) 1
  rw [PadicBerggren.natCast_matrix_mul, PadicBerggren.natCast_matrix_mul, PadicBerggren.N₁_sq] at h01
  simp [Matrix.add_apply, N₁] at h01
  -- `h01 : (m : ZMod (p^k)) * (-2) = 0` up to normalisation
  have h2 : ((2 * m : ℕ) : ZMod (p ^ k)) = 0 := by
    push_cast
    linear_combination h01
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr hodd)
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop h2)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_pow_ne_one_padic (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (B₁ (ZMod (p ^ (k + 1)))) ^ (p ^ k) ≠ 1 := by
  intro h
  have hdvd := PadicBerggren.B₁_order_exact p (k + 1) (p ^ k) hp hodd h
  have hle := Nat.le_of_dvd (Nat.pow_pos hp.pos) hdvd
  have hlt : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_fixes_null_line : B₁ R *ᵥ ![0, 1, 1] = ![0, 1, 1] := by
  funext i
  fin_cases i <;>
    simp [B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₁_fixed_vector : lorentz R ![0, 1, 1] = 0 := by
  simp [lorentz]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_fixes_null_line : B₃ R *ᵥ ![1, 0, 1] = ![1, 0, 1] := by
  funext i
  fin_cases i <;>
    simp [B₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₃_fixed_vector : lorentz R ![1, 0, 1] = 0 := by
  simp [lorentz]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_fixed_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (v : Fin 3 → ZMod p) :
    B₁ (ZMod p) *ᵥ v = v ↔ v = ![0, v 1, v 1] := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    have hv2 : v 2 = v 1 := by
      have : (2 : ZMod p) * (v 2 - v 1) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · linear_combination h
    have hv0 : v 0 = 0 := by
      have : (2 : ZMod p) * v 0 = 0 := by linear_combination h1 - 2 * hv2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · exact h
    funext i
    fin_cases i <;> simp [hv0, hv2]
  · intro h
    rw [h]
    funext i
    fin_cases i <;>
      simp [B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_eq (c : R) : scal2 c = !![c, 0; 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scal2]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_mul (a b : R) : scal2 a * scal2 b = scal2 (a * b) := by
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_pow (a : R) (n : ℕ) : (scal2 a) ^ n = scal2 (a ^ n) := by
  induction n with
  | zero => simp [scal2]
  | succ n ih => rw [pow_succ, ih, PadicBerggren.scal2_mul, pow_succ]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_commute (a : R) (M : Matrix (Fin 2) (Fin 2) R) : Commute (scal2 a) M := by
  unfold Commute SemiconjBy scal2
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_decomp : Um R = scal2 (3 : R) + scal2 (2 : R) * Jm R := by
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Um, Jm]; try ring)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Jm_sq : (Jm R) ^ 2 = scal2 (2 : R) := by
  rw [pow_two]
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_mul_inv : Um R * !![3, -2; -4, 3] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_conj_mul : (scal2 (3 : R) + scal2 (-2 : R) * Jm R) * Um R = 1 := by
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem emb_one : emb (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem emb_mul (A B : Matrix (Fin 2) (Fin 2) R) : emb (A * B) = emb A * emb B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem emb_pow (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : emb (A ^ n) = (emb A) ^ n := by
  induction n with
  | zero => simpa using PadicBerggren.emb_one (R := R)
  | succ n ih => rw [pow_succ, PadicBerggren.emb_mul, ih, pow_succ]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Sm_sq : (Sm R) ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Sm_pow_even {m : ℕ} (hm : Even m) : (Sm R) ^ m = 1 := by
  obtain ⟨t, ht⟩ := hm
  rw [show m = 2 * t by omega, pow_mul, PadicBerggren.Sm_sq, one_pow]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Sm_commute_emb_Um : Commute (Sm R) (emb (Um R)) := by
  unfold Commute SemiconjBy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, emb, Um, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_mul_Wm : B₂ R * Wm R = Wm R * (Sm R * emb (Um R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₂, Wm, Sm, emb, Um, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Wm_mul_Vm : (Wm R) * Vm R = (2 : R) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wm, Vm, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_mul_Wm (n : ℕ) : (B₂ R) ^ n * Wm R = Wm R * (Sm R * emb (Um R)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_assoc, PadicBerggren.B₂_mul_Wm, ← mul_assoc, ih, mul_assoc, ← pow_succ]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_eq_one_of_block (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {m : ℕ}
    (hU : (Um (ZMod p)) ^ m = 1) (hm : Even m) : (B₂ (ZMod p)) ^ m = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have hblock : (Sm (ZMod p) * emb (Um (ZMod p))) ^ m = 1 := by
    rw [Commute.mul_pow PadicBerggren.Sm_commute_emb_Um, PadicBerggren.Sm_pow_even hm, ← PadicBerggren.emb_pow, hU, PadicBerggren.emb_one, one_mul]
  have key : (B₂ (ZMod p)) ^ m * Wm (ZMod p) = Wm (ZMod p) := by
    rw [PadicBerggren.B₂_pow_mul_Wm, hblock, mul_one]
  have key2 : (B₂ (ZMod p)) ^ m * ((2 : ZMod p) • 1) = (2 : ZMod p) • 1 := by
    rw [← PadicBerggren.Wm_mul_Vm, ← mul_assoc, key]
  rw [Matrix.mul_smul, mul_one] at key2
  ext i j
  have := congrFun (congrFun key2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ h2 this

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Jm_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Jm (ZMod p)) ^ p = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hpp : p.Prime := Fact.out
  have h2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have hp' : p = 2 * (p / 2) + 1 := by omega
  calc (Jm (ZMod p)) ^ p = ((Jm (ZMod p)) ^ 2) ^ (p / 2) * Jm (ZMod p) := by
        rw [← pow_mul, ← pow_succ]; exact congrArg _ hp'
    _ = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by rw [PadicBerggren.Jm_sq, PadicBerggren.scal2_pow]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Um (ZMod p)) ^ p
      = scal2 (3 : ZMod p) + scal2 (2 * (2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hcomm : Commute (scal2 (3 : ZMod p)) (scal2 (2 : ZMod p) * Jm (ZMod p)) :=
    scal2_commute _ _
  rw [PadicBerggren.Um_decomp, add_pow_char_of_commute p hcomm,
    Commute.mul_pow (scal2_commute (2 : ZMod p) (Jm (ZMod p))), PadicBerggren.scal2_pow, PadicBerggren.scal2_pow,
    Jm_pow_card p hp, ZMod.pow_card, ZMod.pow_card, ← mul_assoc, PadicBerggren.scal2_mul]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

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

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_p_sub_one_of_isSquare_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : IsSquare (2 : ZMod p)) : (B₂ (ZMod p)) ^ (p - 1) = 1 := by
  have hpp : p.Prime := Fact.out
  have hmod : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have heps : (2 : ZMod p) ^ (p / 2) = 1 := (ZMod.euler_criterion p h2).mp h
  have hUp : (Um (ZMod p)) ^ p = Um (ZMod p) := by
    rw [PadicBerggren.Um_pow_card p hp, heps, mul_one, ← PadicBerggren.Um_decomp]
  have hU : (Um (ZMod p)) ^ (p - 1) = 1 := by
    have hsplit : (Um (ZMod p)) ^ p = (Um (ZMod p)) ^ (p - 1) * Um (ZMod p) := by
      rw [← pow_succ]
      congr 1
      omega
    have : (Um (ZMod p)) ^ (p - 1) * Um (ZMod p) = Um (ZMod p) := by rw [← hsplit, hUp]
    calc (Um (ZMod p)) ^ (p - 1)
        = (Um (ZMod p)) ^ (p - 1) * (Um (ZMod p) * !![3, -2; -4, 3]) := by
          rw [PadicBerggren.Um_mul_inv, mul_one]
      _ = ((Um (ZMod p)) ^ (p - 1) * Um (ZMod p)) * !![3, -2; -4, 3] := by rw [mul_assoc]
      _ = Um (ZMod p) * !![3, -2; -4, 3] := by rw [this]
      _ = 1 := PadicBerggren.Um_mul_inv
  refine PadicBerggren.B₂_pow_eq_one_of_block p hp hU ?_
  exact (Nat.even_sub (by omega)).mpr (by simp [Nat.not_even_iff.mpr hmod])

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_p_add_one_of_not_isSquare_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : ¬ IsSquare (2 : ZMod p)) : (B₂ (ZMod p)) ^ (p + 1) = 1 := by
  have hpp : p.Prime := Fact.out
  have hmod : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have heps : (2 : ZMod p) ^ (p / 2) = -1 := by
    rcases PadicBerggren.two_pow_div_two_eq p hp with h1 | h1
    · exact absurd ((ZMod.euler_criterion p h2).mpr h1) h
    · exact h1
  have hU : (Um (ZMod p)) ^ (p + 1) = 1 := by
    rw [pow_succ, PadicBerggren.Um_pow_card p hp, heps]
    have : (2 : ZMod p) * (-1) = -2 := by ring
    rw [this]
    exact PadicBerggren.Um_conj_mul
  refine PadicBerggren.B₂_pow_eq_one_of_block p hp hU ?_
  exact Nat.even_add_one.mpr (Nat.not_even_iff.mpr hmod)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_card_sq_sub_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (B₂ (ZMod p)) ^ (p ^ 2 - 1) = 1 := by
  have hpp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hpp.one_lt.le.trans' (by omega)
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have := Nat.sq_sub_sq p 1
    simpa using this
  by_cases h : IsSquare (2 : ZMod p)
  · rw [hfac, mul_comm, pow_mul, PadicBerggren.B₂_pow_p_sub_one_of_isSquare_two p hp h, one_pow]
  · rw [hfac, pow_mul, PadicBerggren.B₂_pow_p_add_one_of_not_isSquare_two p hp h, one_pow]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_orderOf_dvd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    orderOf (B₂ (ZMod p)) ∣ p ^ 2 - 1 :=
  orderOf_dvd_of_pow_eq_one (PadicBerggren.B₂_pow_card_sq_sub_one p hp)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_no_nonzero_fixed_point (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (v : Fin 3 → ZMod p) (h : B₂ (ZMod p) *ᵥ v = v) : v = 0 := by
  have hpp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2' := congrFun h 2
  simp [B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2'
  have e0 : (2 : ZMod p) * (v 1 + v 2) = 0 := by linear_combination h0
  have e1 : (2 : ZMod p) * (v 0 + v 2) = 0 := by linear_combination h1
  have e2 : (2 : ZMod p) * (v 0 + v 1 + v 2) = 0 := by linear_combination h2'
  have f0 : v 1 + v 2 = 0 := by
    rcases mul_eq_zero.mp e0 with hh | hh
    · exact absurd hh h2
    · exact hh
  have f1 : v 0 + v 2 = 0 := by
    rcases mul_eq_zero.mp e1 with hh | hh
    · exact absurd hh h2
    · exact hh
  have f2 : v 0 + v 1 + v 2 = 0 := by
    rcases mul_eq_zero.mp e2 with hh | hh
    · exact absurd hh h2
    · exact hh
  have hv2 : v 2 = 0 := by linear_combination f0 + f1 - f2
  have hv1 : v 1 = 0 := by linear_combination f0 - hv2
  have hv0 : v 0 = 0 := by linear_combination f1 - hv2
  funext i
  fin_cases i <;> simp [hv0, hv1, hv2]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_null_eigenvector_iff_isSquare_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∃ (lam : ZMod p) (v : Fin 3 → ZMod p), v ≠ 0 ∧ lorentz (ZMod p) v = 0 ∧
      B₂ (ZMod p) *ᵥ v = lam • v) ↔ IsSquare (2 : ZMod p) := by
  have hpp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  constructor
  · rintro ⟨lam, v, hv0, hvnull, hveq⟩
    have hker : (B₂ (ZMod p) - lam • (1 : Matrix (Fin 3) (Fin 3) (ZMod p))) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, hveq]
      funext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]
    have hdet : (B₂ (ZMod p) - lam • (1 : Matrix (Fin 3) (Fin 3) (ZMod p))).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩
    have hpoly : (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0 := by
      rw [Matrix.det_fin_three] at hdet
      simp [B₂, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hdet
      linear_combination -hdet
    rcases mul_eq_zero.mp hpoly with hlam | hlam
    · -- eigenvalue −1: its eigenline `(t,−t,0)` is not null
      exfalso
      have hlam' : lam = -1 := by linear_combination hlam
      subst hlam'
      have h0 := congrFun hveq 0
      have h1 := congrFun hveq 1
      have h2' := congrFun hveq 2
      simp [B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2'
      have e2 : (2 : ZMod p) * v 2 = 0 := by linear_combination h2' - h0
      have hv2 : v 2 = 0 := by
        rcases mul_eq_zero.mp e2 with hh | hh
        · exact absurd hh h2
        · exact hh
      have esum : (2 : ZMod p) * (v 0 + v 1) = 0 := by linear_combination h0 - 2 * hv2
      have hsum : v 0 + v 1 = 0 := by
        rcases mul_eq_zero.mp esum with hh | hh
        · exact absurd hh h2
        · exact hh
      have hv1 : v 1 = -v 0 := by linear_combination hsum
      have hnull : (2 : ZMod p) * (v 0 * v 0) = 0 := by
        simp [lorentz, hv1, hv2] at hvnull
        linear_combination hvnull
      have hv0' : v 0 = 0 := by
        rcases mul_eq_zero.mp hnull with hh | hh
        · exact absurd hh h2
        · exact (mul_self_eq_zero.mp hh)
      apply hv0
      funext i
      fin_cases i <;> simp [hv0', hv1, hv2]
    · -- eigenvalue 3 ± 2√2 forces 2 to be a square
      refine ⟨(lam - 3) / 2, ?_⟩
      field_simp
      linear_combination -hlam
  · rintro ⟨s, hs⟩
    refine ⟨3 + 2 * s, ![1, 1, s], ?_, ?_, ?_⟩
    · intro hcon
      have := congrFun hcon 0
      simp at this
    · simp [lorentz]
      linear_combination hs
    · funext i
      fin_cases i <;>
        simp [B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
        first
          | ring1
          | linear_combination (2 : ZMod p) * hs

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_null_eigenvector_iff_mod_eight (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∃ (lam : ZMod p) (v : Fin 3 → ZMod p), v ≠ 0 ∧ lorentz (ZMod p) v = 0 ∧
      B₂ (ZMod p) *ᵥ v = lam • v) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  (PadicBerggren.B₂_null_eigenvector_iff_isSquare_two p hp).trans (ZMod.exists_sq_eq_two_iff hp)

end

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem mono {d e : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (h : d ∣ e) (hA : EntryDvd e A) :
    EntryDvd d A := fun i j => h.trans (hA i j)

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem add {d : ℤ} {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A) (hB : EntryDvd d B) :
    EntryDvd d (A + B) := fun i j => by
  simpa [Matrix.add_apply] using dvd_add (hA i j) (hB i j)

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem mul {d e : ℤ} {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A)
    (hB : EntryDvd e B) : EntryDvd (d * e) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => mul_dvd_mul (hA i k) (hB k j)

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem mul_right {d : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A)
    (B : Matrix (Fin 3) (Fin 3) ℤ) : EntryDvd d (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (hA i k) _

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem entryDvd_mulVec {d : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (h : EntryDvd d A)
    (v : Fin 3 → ℤ) (i : Fin 3) : d ∣ (A *ᵥ v) i := by
  have hsum : (A *ᵥ v) i = ∑ j : Fin 3, A i j * v j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hsum]
  exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (h i j) _

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem pow_one_add_eq {S : Type*} [Ring S] (X : S) (n : ℕ) :
    ∃ C : S, (1 + X) ^ n = 1 + (n : S) * X + X ^ 2 * C := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨C + (n : S) + C * X, ?_⟩
      have hcom : (n : S) * X * X = X ^ 2 * (n : S) := by
        rw [mul_assoc, ← pow_two]
        exact (Nat.cast_commute n (X ^ 2)).eq
      have expand : (1 + (n : S) * X + X ^ 2 * C) * (1 + X)
          = (1 + ((n : S) + 1) * X + X ^ 2 * (C + (n : S) + C * X))
            + ((n : S) * X * X - X ^ 2 * (n : S)) := by
        noncomm_ring
      rw [pow_succ, hC, expand, hcom]
      push_cast
      noncomm_ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem natCast_matrix_mul_int (m : ℕ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    ((m : Matrix (Fin 3) (Fin 3) ℤ)) * M = (m : ℤ) • M := PadicBerggren.natCast_matrix_mul m M

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lift_step (A : Matrix (Fin 3) (Fin 3) ℤ) (p j : ℕ) (hj : 1 ≤ j)
    (h : EntryDvd ((p : ℤ) ^ j) (A - 1)) : EntryDvd ((p : ℤ) ^ (j + 1)) (A ^ p - 1) := by
  obtain ⟨C, hC⟩ := PadicBerggren.pow_one_add_eq (A - 1) p
  have hA : (1 : Matrix (Fin 3) (Fin 3) ℤ) + (A - 1) = A := by
    rw [add_sub_cancel]
  rw [hA] at hC
  have hsplit : A ^ p - 1
      = (p : Matrix (Fin 3) (Fin 3) ℤ) * (A - 1) + (A - 1) ^ 2 * C := by
    rw [hC]
    noncomm_ring
  rw [hsplit]
  refine EntryDvd.add ?_ ?_
  · rw [PadicBerggren.natCast_matrix_mul_int]
    intro i j'
    rw [Matrix.smul_apply, smul_eq_mul, pow_succ']
    exact mul_dvd_mul_left _ (h i j')
  · have hsq : EntryDvd ((p : ℤ) ^ j * (p : ℤ) ^ j) ((A - 1) ^ 2) := by
      rw [pow_two]
      exact h.mul h
    have hprod : EntryDvd ((p : ℤ) ^ j * (p : ℤ) ^ j) ((A - 1) ^ 2 * C) := hsq.mul_right C
    refine EntryDvd.mono ?_ hprod
    rw [← pow_add]
    exact pow_dvd_pow _ (by omega)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lift_pow (A : Matrix (Fin 3) (Fin 3) ℤ) (p : ℕ) (h : EntryDvd (p : ℤ) (A - 1))
    (k : ℕ) : EntryDvd ((p : ℤ) ^ (k + 1)) (A ^ (p ^ k) - 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hstep := PadicBerggren.lift_step (A ^ (p ^ k)) p (k + 1) (by omega) ih
      rwa [← pow_mul, ← pow_succ] at hstep

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem redRing_B₂ (m : ℕ) : redRing m (B₂ ℤ) = B₂ (ZMod m) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redRing, RingHom.mapMatrix_apply, B₂]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem entryDvd_iff_red (m : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) :
    EntryDvd (m : ℤ) A ↔ redRing m A = 0 := by
  constructor
  · intro h
    ext i j
    simpa [redRing, RingHom.mapMatrix_apply] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (A i j) m).mpr (h i j)
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [redRing, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Int.coe_castRingHom] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (A i j) m).mp this

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_int_pow_sub_one_dvd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    EntryDvd (p : ℤ) ((B₂ ℤ) ^ (p ^ 2 - 1) - 1) := by
  rw [PadicBerggren.entryDvd_iff_red]
  rw [map_sub, map_pow, map_one, PadicBerggren.redRing_B₂, PadicBerggren.B₂_pow_card_sq_sub_one p hp, sub_self]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_eq_one_padic (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (B₂ (ZMod (p ^ (k + 1)))) ^ ((p ^ 2 - 1) * p ^ k) = 1 := by
  have hlift := PadicBerggren.lift_pow ((B₂ ℤ) ^ (p ^ 2 - 1)) p (PadicBerggren.B₂_int_pow_sub_one_dvd p hp) k
  rw [← pow_mul] at hlift
  have hcast : ((p : ℤ) ^ (k + 1)) = ((p ^ (k + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, PadicBerggren.entryDvd_iff_red] at hlift
  rw [map_sub, map_pow, map_one, PadicBerggren.redRing_B₂] at hlift
  have := sub_eq_zero.mp hlift
  exact this

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_padic_contraction (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (v : Fin 3 → ℤ) (i : Fin 3) :
    ((p : ℤ) ^ (k + 1)) ∣ (((B₂ ℤ) ^ ((p ^ 2 - 1) * p ^ k)) *ᵥ v) i - v i := by
  have hlift := PadicBerggren.lift_pow ((B₂ ℤ) ^ (p ^ 2 - 1)) p (PadicBerggren.B₂_int_pow_sub_one_dvd p hp) k
  rw [← pow_mul] at hlift
  have key := PadicBerggren.entryDvd_mulVec hlift v i
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at key

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_int_pow_sub_one (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    EntryDvd ((p : ℤ) ^ k) ((B₁ ℤ) ^ (p ^ k) - 1) := by
  have hform := PadicBerggren.pow_unipotent_formula (N₁ ℤ) PadicBerggren.N₁_cube (p ^ k)
  rw [← PadicBerggren.B₁_eq_one_add] at hform
  have hsub : (B₁ ℤ) ^ (p ^ k) - 1
      = ((p ^ k : ℕ) : Matrix (Fin 3) (Fin 3) ℤ) * N₁ ℤ
        + (((p ^ k).choose 2 : ℕ) : Matrix (Fin 3) (Fin 3) ℤ) * (N₁ ℤ) ^ 2 := by
    rw [hform]
    noncomm_ring
  rw [hsub]
  refine EntryDvd.add ?_ ?_
  · rw [PadicBerggren.natCast_matrix_mul_int]
    intro i j
    refine ⟨(N₁ ℤ) i j, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  · obtain ⟨t, ht⟩ := PadicBerggren.pow_dvd_choose_two p k hp hodd
    rw [PadicBerggren.natCast_matrix_mul_int]
    intro i j
    refine ⟨(t : ℤ) * ((N₁ ℤ) ^ 2) i j, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, ht]
    push_cast
    ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_padic_contraction (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (v : Fin 3 → ℤ) (i : Fin 3) :
    ((p : ℤ) ^ k) ∣ (((B₁ ℤ) ^ (p ^ k)) *ᵥ v) i - v i := by
  have key := PadicBerggren.entryDvd_mulVec (PadicBerggren.B₁_int_pow_sub_one p k hp hodd) v i
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at key

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_B₂_noncommute (p : ℕ) [hp' : Fact p.Prime] (hp : p ≠ 2) :
    B₁ (ZMod p) * B₂ (ZMod p) ≠ B₂ (ZMod p) * B₁ (ZMod p) := by
  intro h
  have h00 : (B₁ (ZMod p) * B₂ (ZMod p)) 0 0 = (B₂ (ZMod p) * B₁ (ZMod p)) 0 0 := by rw [h]
  have e1 : (B₁ (ZMod p) * B₂ (ZMod p)) 0 0 = 1 := by
    simp [B₁, B₂, Matrix.mul_apply, Fin.sum_univ_three]
  have e2 : (B₂ (ZMod p) * B₁ (ZMod p)) 0 0 = 9 := by
    simp [B₂, B₁, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  rw [e1, e2] at h00
  have h8 : ((8 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination -h00
  have hdvd : p ∣ 8 := (ZMod.natCast_eq_zero_iff _ _).mp h8
  have hdvd2 : p ∣ 2 ^ 3 := by simpa using hdvd
  exact hp ((Nat.prime_dvd_prime_iff_eq hp'.out Nat.prime_two).mp
    (hp'.out.dvd_of_dvd_pow hdvd2))

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_orbit_periodic (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (v : Fin 3 → ZMod (p ^ (k + 1))) :
    (B₂ (ZMod (p ^ (k + 1)))) ^ ((p ^ 2 - 1) * p ^ k) *ᵥ v = v := by
  rw [PadicBerggren.B₂_pow_eq_one_padic p k hp, Matrix.one_mulVec]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_root : lorentz R (root R) = 0 := by
  simp [lorentz, root]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_gen (i : Fin 3) (v : Fin 3 → R) : lorentz R (gen R i *ᵥ v) = lorentz R v := by
  fin_cases i <;>
    simp [gen, lorentz, B₁, B₂, B₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_wordMat (w : List (Fin 3)) :
    lorentz R (wordMat R w *ᵥ root R) = 0 := by
  induction w with
  | nil => simpa [wordMat, Matrix.one_mulVec] using PadicBerggren.lorentz_root (R := R)
  | cons a w ih =>
      have hstep : wordMat R (a :: w) *ᵥ root R = gen R a *ᵥ (wordMat R w *ᵥ root R) := by
        simp [wordMat, List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]
      rw [hstep, PadicBerggren.lorentz_gen]
      exact ih

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem tree_collision_mod (m d : ℕ) [NeZero m] (h : m ^ 3 < 3 ^ d) :
    ∃ w₁ w₂ : Fin d → Fin 3, w₁ ≠ w₂ ∧
      wordMat (ZMod m) (List.ofFn w₁) *ᵥ root (ZMod m)
        = wordMat (ZMod m) (List.ofFn w₂) *ᵥ root (ZMod m) := by
  have hcard : Fintype.card (Fin 3 → ZMod m) < Fintype.card (Fin d → Fin 3) := by
    simpa [Fintype.card_fun, ZMod.card] using h
  obtain ⟨w₁, w₂, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun w : Fin d → Fin 3 => wordMat (ZMod m) (List.ofFn w) *ᵥ root (ZMod m)) hcard
  exact ⟨w₁, w₂, hne, heq⟩

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem mem_nullConeFinset (w : Fin 3 → ZMod p) :
    w ∈ nullConeFinset p ↔ w ∈ nullCone (ZMod p) := by
  simp [nullConeFinset, nullCone, Set.mem_setOf_eq]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

omit [Fact p.Prime] in

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem eta3 (w : Fin 3 → ZMod p) : w = ![w 0, w 1, w 2] := by
  funext i; fin_cases i <;> rfl

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem card_nullCone_fiber (hp : p ≠ 2) (u : ZMod p) :
    ((nullConeFinset p).filter (fun w => w 2 - w 0 = u)).card = p := by
  have h2 : (2 : ZMod p) ≠ 0 := PadicBerggren.two_ne_zero_zmod p hp
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
        rw [hA, hC, ← PadicBerggren.eta3 p w]
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

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem card_nullCone (hp : p ≠ 2) : (nullConeFinset p).card = p ^ 2 := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun w : Fin 3 → ZMod p => w 2 - w 0) (s := nullConeFinset p)
    (t := (univ : Finset (ZMod p))) (fun x _ => mem_univ _)
  rw [hfib, Finset.sum_congr rfl (fun u _ => PadicBerggren.card_nullCone_fiber p hp u),
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, sq]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem zero_mem_nullConeFinset : (0 : Fin 3 → ZMod p) ∈ nullConeFinset p := by
  simp [nullConeFinset, lorentz]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem card_nullCone_nonzero (hp : p ≠ 2) :
    ((nullConeFinset p).erase 0).card = p ^ 2 - 1 := by
  rw [Finset.card_erase_of_mem (PadicBerggren.zero_mem_nullConeFinset p), PadicBerggren.card_nullCone p hp]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem tree_collision_nullCone (d : ℕ) (hp : p ≠ 2) (h : p ^ 2 < 3 ^ d) :
    ∃ w₁ w₂ : Fin d → Fin 3, w₁ ≠ w₂ ∧
      wordMat (ZMod p) (List.ofFn w₁) *ᵥ root (ZMod p)
        = wordMat (ZMod p) (List.ofFn w₂) *ᵥ root (ZMod p) := by
  have hcard : (nullConeFinset p).card < (univ : Finset (Fin d → Fin 3)).card := by
    rw [PadicBerggren.card_nullCone p hp, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    exact h
  have hmaps : ∀ w : Fin d → Fin 3, w ∈ (univ : Finset (Fin d → Fin 3)) →
      wordMat (ZMod p) (List.ofFn w) *ᵥ root (ZMod p) ∈ nullConeFinset p := by
    intro w _
    simp only [nullConeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact PadicBerggren.lorentz_wordMat (R := ZMod p) (List.ofFn w)
  obtain ⟨w₁, -, w₂, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  exact ⟨w₁, w₂, hne, heq⟩

end

end PadicBerggren

namespace PadicBerggren

theorem pow_mod_eq {M : Type*} [Monoid M] (x : M) (m : ℕ) (hm : x ^ m = 1) (n : ℕ) :
    x ^ n = x ^ (n % m) := by
  conv_lhs => rw [← Nat.div_add_mod n m]
  rw [pow_add, pow_mul, hm, one_pow, one_mul]

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

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
  · exact ⟨p - 1, by omega, by omega, PadicBerggren.B₂_pow_p_sub_one_of_isSquare_two p hp h⟩
  · exact ⟨p + 1, by omega, le_rfl, PadicBerggren.B₂_pow_p_add_one_of_not_isSquare_two p hp h⟩

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem B₂_orbit_card_le (hp : p ≠ 2) (v : Fin 3 → ZMod p) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ p + 1 ∧
      ∀ n : ℕ, ∃ r < m, (B₂ (ZMod p)) ^ n *ᵥ v = (B₂ (ZMod p)) ^ r *ᵥ v := by
  obtain ⟨m, hm1, hm2, hm⟩ := PadicBerggren.B₂_pow_le_p_add_one p hp
  refine ⟨m, hm1, hm2, fun n => ⟨n % m, Nat.mod_lt _ (by omega), ?_⟩⟩
  rw [PadicBerggren.pow_mod_eq (B₂ (ZMod p)) m hm n]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem B₂_not_transitive_on_nullCone (hp : p ≠ 2) (v : Fin 3 → ZMod p) :
    ¬ (∀ w ∈ (nullConeFinset p).erase 0, ∃ n : ℕ, (B₂ (ZMod p)) ^ n *ᵥ v = w) := by
  intro htrans
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp
    · exact h
  obtain ⟨m, hm1, hm2, hred⟩ := PadicBerggren.B₂_orbit_card_le p hp v
  have hsub : (nullConeFinset p).erase 0 ⊆
      Finset.image (fun n : ℕ => (B₂ (ZMod p)) ^ n *ᵥ v) (Finset.range m) := by
    intro w hw
    obtain ⟨n, hn⟩ := htrans w hw
    obtain ⟨r, hr, hrn⟩ := hred n
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by rw [← hrn, hn]⟩
  have hcard : ((nullConeFinset p).erase 0).card ≤ m :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_image_le) (by simp))
  rw [PadicBerggren.card_nullCone_nonzero p hp] at hcard
  have hsq : p + 3 ≤ p ^ 2 := by nlinarith
  omega

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem eigenvalue_norm_one (s : ZMod p) (hs : (2 : ZMod p) = s * s) :
    (3 + 2 * s) * (3 - 2 * s) = 1 := by
  linear_combination (4 : ZMod p) * hs

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem lorentz_eigenvector (s : ZMod p) (hs : (2 : ZMod p) = s * s) :
    lorentz (ZMod p) ![1, 1, s] = 0 := by
  simp [lorentz]
  linear_combination hs

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem B₂_mulVec_eigenvector (s : ZMod p) (hs : (2 : ZMod p) = s * s) :
    B₂ (ZMod p) *ᵥ ![1, 1, s] = (3 + 2 * s) • ![1, 1, s] := by
  funext i
  fin_cases i <;>
    simp [B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination (2 : ZMod p) * hs

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem B₂_pow_mulVec_eigenvector (s : ZMod p) (hs : (2 : ZMod p) = s * s) (n : ℕ) :
    (B₂ (ZMod p)) ^ n *ᵥ ![1, 1, s] = ((3 + 2 * s) ^ n) • ![1, 1, s] := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (B₂ (ZMod p)) ^ (n + 1) *ᵥ ![1, 1, s]
          = B₂ (ZMod p) *ᵥ ((B₂ (ZMod p)) ^ n *ᵥ ![1, 1, s]) := by
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      rw [hstep, ih, Matrix.mulVec_smul, PadicBerggren.B₂_mulVec_eigenvector p s hs, smul_smul, ← pow_succ]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem B₂_eigenvector_period (s : ZMod p) (hs : (2 : ZMod p) = s * s) (n : ℕ) :
    (B₂ (ZMod p)) ^ n *ᵥ ![1, 1, s] = ![1, 1, s] ↔ (3 + 2 * s) ^ n = 1 := by
  rw [PadicBerggren.B₂_pow_mulVec_eigenvector p s hs]
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa using h0
  · intro h
    rw [h, one_smul]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem card_B₁_fixedPoints (hp : p ≠ 2) :
    ((univ : Finset (Fin 3 → ZMod p)).filter
      (fun w => B₁ (ZMod p) *ᵥ w = w)).card = p := by
  have hinj : Function.Injective (fun t : ZMod p => (![0, t, t] : Fin 3 → ZMod p)) := by
    intro a b hab
    have := congrFun hab 1
    simpa using this
  have himg : ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₁ (ZMod p) *ᵥ w = w))
      = Finset.image (fun t : ZMod p => (![0, t, t] : Fin 3 → ZMod p)) univ := by
    ext w
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · intro hw
      exact ⟨w 1, ((PadicBerggren.B₁_fixed_iff p hp w).mp hw).symm⟩
    · rintro ⟨t, rfl⟩
      refine (PadicBerggren.B₁_fixed_iff p hp _).mpr ?_
      funext i
      fin_cases i <;> simp
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem B₁_fixedPoints_subset_nullCone (hp : p ≠ 2) :
    ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₁ (ZMod p) *ᵥ w = w))
      ⊆ nullConeFinset p := by
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw
  have hform := (PadicBerggren.B₁_fixed_iff p hp w).mp hw
  simp only [nullConeFinset, mem_filter, mem_univ, true_and, lorentz]
  rw [hform]
  simp

end

end PadicBerggren

namespace PadicBerggren

section
variable (p : ℕ) [Fact p.Prime]

theorem fixedPoint_dichotomy (hp : p ≠ 2) :
    ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₁ (ZMod p) *ᵥ w = w)).card = p ∧
    ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₂ (ZMod p) *ᵥ w = w)).card = 1 := by
  refine ⟨PadicBerggren.card_B₁_fixedPoints p hp, ?_⟩
  have hset : ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₂ (ZMod p) *ᵥ w = w))
      = {0} := by
    ext w
    simp only [mem_filter, mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hw
      exact PadicBerggren.B₂_no_nonzero_fixed_point p hp w hw
    · rintro rfl
      simp
  rw [hset, Finset.card_singleton]

end

end PadicBerggren


theorem solution (hp : p ≠ 2) :
    ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₁ (ZMod p) *ᵥ w = w)).card = p ∧
    ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₂ (ZMod p) *ᵥ w = w)).card = 1 := by
  refine ⟨PadicBerggren.card_B₁_fixedPoints p hp, ?_⟩
  have hset : ((univ : Finset (Fin 3 → ZMod p)).filter (fun w => B₂ (ZMod p) *ᵥ w = w))
      = {0} := by
    ext w
    simp only [mem_filter, mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hw
      exact PadicBerggren.B₂_no_nonzero_fixed_point p hp w hw
    · rintro rfl
      simp
  rw [hset, Finset.card_singleton]

#print axioms solution
