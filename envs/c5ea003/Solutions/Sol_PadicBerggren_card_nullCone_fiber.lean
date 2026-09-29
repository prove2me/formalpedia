-- Prove2me | solution 1 for PadicBerggren.card_nullCone_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:36.059792+00:00
-- url     : https://prove2.me/submissions/ce011b7d-611c-4433-bc42-0eb6f48c631a

-- Sol generated from Geometry/PadicBerggrenNullCone.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Definitions.Def_Geometry_PadicBerggrenNullCone

/-!
# The size of the p-adic Berggren null cone

`Catalog/Geometry/PadicBerggrenDynamics.lean` sets up the three Berggren (Barning–Hall)
generators as a dynamical system on `(ZMod (p^k))³` preserving the Lorentz form
`q(a,b,c) = a² + b² − c²`.  Every state of that system lives on the **null cone**
`q = 0`, and the whole Berggren tree reduces into it.

This file computes the exact size of the phase space:

* `PadicBerggren.card_nullCone` : for every odd prime `p` the null cone mod `p` has
  **exactly `p²` points**.  The proof fibres the cone over the linear functional
  `w ↦ w 2 − w 0` (the "light-cone coordinate" `c − a`) and shows that *every* fibre —
  including the degenerate one over `0` — has exactly `p` points.  This is the counting
  incarnation of the fact that `q` is a nondegenerate isotropic ternary form.
* `PadicBerggren.card_nullCone_nonzero` : `p² − 1` nonzero null vectors, i.e. `p + 1`
  projective null points each carrying `p − 1` nonzero vectors.
* `PadicBerggren.tree_collision_nullCone` : since the whole depth-`d` tree lands inside the
  null cone, two distinct words already collide mod `p` as soon as `3^d > p²`.  This is a
  quadratic (in `p`) obstruction, far stronger than the naive cubic bound
  `tree_collision_mod`, and it says that the reduction of the boundary of the tree has
  "box dimension at most 2": the tree cannot inject into any single finite level.
-/

open PadicBerggren

open Matrix Finset

variable (p : ℕ) [Fact p.Prime]



/-- `2` is invertible mod an odd prime. -/
theorem two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

omit [Fact p.Prime] in
/-- Eta-expansion of a vector of length three. -/
theorem eta3 (w : Fin 3 → ZMod p) : w = ![w 0, w 1, w 2] := by
  funext i; fin_cases i <;> rfl







open PadicBerggren in
theorem solution(hp : p ≠ 2) (u : ZMod p) :
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
