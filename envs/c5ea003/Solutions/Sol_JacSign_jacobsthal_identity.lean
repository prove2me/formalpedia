-- Prove2me | solution 1 for JacSign.jacobsthal_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:15:12.662791+00:00
-- url     : https://prove2.me/submissions/b69c8dfb-7a5b-408d-aaca-1f065f2fae50

-- Sol generated from Tropical/JacobiSignedTwoSquares.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Theorems.Thm_JacSign_A_zero
import Theorems.Thm_JacSign_chi_cube
import Theorems.Thm_JacSign_moment

/-!
# The Weil floor is a two-squares identity

The Weil bound `W p ^ 2 ≤ 4 p` of `JacobiSignedWeilFloorBound.lean` is not an accident of
estimation: it is the shadow of an **exact identity**.  Write `A p d = ∑_x χ(x³ - d x)` for
the twisted character sums, and let `ν` be any quadratic nonresidue mod `p`.  For
`p ≡ 1 (mod 4)` we prove

`A p 1 ^ 2 + A p ν ^ 2 = 4 p`   (`JacSign.jacobsthal_identity`)

so the Jacobi-signed circle count `W p = A p 1` and its nonresidue twin `A p ν` are the two
legs of a right triangle with hypotenuse `2 √p`.  Consequences:

* `JacSign.W_sq_add_twist_sq` : the identity phrased for the statistic `W p` itself;
* `JacSign.weil_floor_of_identity` : the Weil bound, re-derived as a corollary;
* `JacSign.two_squares_of_one_mod_four` : **Fermat's two-square theorem** with explicit
  witnesses `p = (W p / 2)² + (A p ν / 2)²` — the signal and its twin are *exactly* the
  Gaussian-integer coordinates of `p`.

Structurally this explains the experimental data: `W p` is `2a` where `p = a² + b²`, hence
its erratic, "unstructured" behaviour, and hence also its inability to leak the factors of
a semiprime — the two legs trade off against each other with `4p` conserved.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]

/-- Counting square roots: pushing a sum forward along `c ↦ c²` weights each point by
`χ(d) + 1`, the number of square roots of `d`. -/
theorem sum_sq_comp (hp : p ≠ 2) (F : ZMod p → ℤ) :
    ∑ c : ZMod p, F (c ^ 2) = ∑ d : ZMod p, (quadraticChar (ZMod p) d + 1) * F d := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have key : ∀ a : ZMod p,
      ((univ.filter (fun y : ZMod p => y ^ 2 = a)).card : ℤ) = quadraticChar (ZMod p) a + 1 := by
    intro a
    simpa [Set.toFinset_setOf] using quadraticChar_card_sqrts (F := ZMod p) hF a
  have h1 : ∀ c : ZMod p, F (c ^ 2) = ∑ d : ZMod p, if c ^ 2 = d then F d else 0 := by
    intro c; simp
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← key d]

/-- Scaling a twist by a square multiplies the character sum by `χ(c)`. -/
theorem A_scale {c : ZMod p} (hc : c ≠ 0) (e : ZMod p) :
    A p (c ^ 2 * e) = quadraticChar (ZMod p) c * A p e := by
  have hre : A p (c ^ 2 * e)
      = ∑ u : ZMod p, quadraticChar (ZMod p) ((c * u) ^ 3 - (c ^ 2 * e) * (c * u)) := by
    rw [A]
    exact (Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ fun u => rfl).symm
  rw [hre, A, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show (c * u) ^ 3 - (c ^ 2 * e) * (c * u) = c ^ 3 * (u ^ 3 - e * u) by ring, map_mul, chi_cube]







open JacSign in
theorem solution(hp : p ≠ 2) (h1 : p % 4 = 1) {v : ZMod p}
    (hv : quadraticChar (ZMod p) v = -1) : (A p 1) ^ 2 + (A p v) ^ 2 = 4 * (p : ℤ) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, MulChar.map_zero] at hv
    exact absurd hv (by norm_num)
  have hvinv : quadraticChar (ZMod p) v⁻¹ = -1 := by
    have hmul : quadraticChar (ZMod p) v * quadraticChar (ZMod p) v⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hv0, MulChar.map_one]
    rw [hv] at hmul
    linarith
  set F : ZMod p → ℤ := fun d => (A p d) ^ 2 with hF
  have hF0 : F 0 = 0 := by rw [hF]; simp [A_zero p hp]
  -- push the second moment forward along squaring, twice
  have hres : ∑ c : ZMod p, F (c ^ 2) = ((p : ℤ) - 1) * (A p 1) ^ 2 := by
    have hval : ∀ c : ZMod p, F (c ^ 2) = if c = 0 then 0 else (A p 1) ^ 2 := by
      intro c
      by_cases hc : c = 0
      · rw [hc, if_pos rfl]; simpa using hF0
      · rw [if_neg hc, hF]
        simp only
        rw [show c ^ 2 = c ^ 2 * 1 by ring, A_scale p hc 1, mul_pow, quadraticChar_sq_one hc,
          one_mul]
    rw [Finset.sum_congr rfl fun c _ => hval c, Finset.sum_ite]
    have hset : (univ.filter (fun x : ZMod p => ¬ x = 0)) = univ.erase 0 := by
      ext x; simp [Finset.mem_erase, and_comm]
    rw [Finset.sum_const, Finset.sum_const, hset,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
    simp only [smul_zero, zero_add, nsmul_eq_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hnonres : ∑ c : ZMod p, F (v * c ^ 2) = ((p : ℤ) - 1) * (A p v) ^ 2 := by
    have hval : ∀ c : ZMod p, F (v * c ^ 2) = if c = 0 then 0 else (A p v) ^ 2 := by
      intro c
      by_cases hc : c = 0
      · rw [hc, if_pos rfl]; simpa using hF0
      · rw [if_neg hc, hF]
        simp only
        rw [show v * c ^ 2 = c ^ 2 * v by ring, A_scale p hc v, mul_pow,
          quadraticChar_sq_one hc, one_mul]
    rw [Finset.sum_congr rfl fun c _ => hval c, Finset.sum_ite]
    have hset : (univ.filter (fun x : ZMod p => ¬ x = 0)) = univ.erase 0 := by
      ext x; simp [Finset.mem_erase, and_comm]
    rw [Finset.sum_const, Finset.sum_const, hset,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
    simp only [smul_zero, zero_add, nsmul_eq_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  -- the two forward pushes have complementary weights
  have hw1 : ∑ c : ZMod p, F (c ^ 2)
      = ∑ d : ZMod p, (quadraticChar (ZMod p) d + 1) * F d := sum_sq_comp p hp F
  have hw2 : ∑ c : ZMod p, F (v * c ^ 2)
      = ∑ d : ZMod p, (1 - quadraticChar (ZMod p) d) * F d := by
    have hstep : ∑ c : ZMod p, F (v * c ^ 2)
        = ∑ d : ZMod p, (quadraticChar (ZMod p) d + 1) * F (v * d) :=
      sum_sq_comp p hp (fun d => F (v * d))
    rw [hstep]
    refine Fintype.sum_equiv (Equiv.mulLeft₀ v hv0) _ _ fun d => ?_
    show (quadraticChar (ZMod p) d + 1) * F (v * d)
        = (1 - quadraticChar (ZMod p) (v * d)) * F (v * d)
    rw [map_mul, hv]
    ring
  have hsum : ((p : ℤ) - 1) * (A p 1) ^ 2 + ((p : ℤ) - 1) * (A p v) ^ 2
      = 2 * ∑ d : ZMod p, F d := by
    rw [← hres, ← hnonres, hw1, hw2, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hmom : ∑ d : ZMod p, F d = 2 * (p : ℤ) * ((p : ℤ) - 1) := moment p hp h1
  rw [hmom] at hsum
  have hpos : (0 : ℤ) < (p : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
    linarith
  have : ((p : ℤ) - 1) * ((A p 1) ^ 2 + (A p v) ^ 2) = ((p : ℤ) - 1) * (4 * (p : ℤ)) := by
    linarith
  exact mul_left_cancel₀ (ne_of_gt hpos) this
