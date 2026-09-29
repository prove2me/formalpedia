-- Prove2me | solution 1 for mme_dwz_conditioned_XZ_collision_fiber_independent_of_b0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:08:14.275763+00:00
-- url     : https://prove2.me/submissions/afbd1dc3-c7af-42da-ab1e-a52f753865ff

import Definitions.Def_mme_dwz_asymmetric_affine_hash

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem conditioned_hash_eq_independent_of_b0
    {p N : ℕ} (b0 b0' w0 : ZMod p)
    (w : Fin (N + 1) → ZMod p)
    (X Z : Fin (N + 1) → Fin 5) :
    (b0 + ∑ t, ((X t).val : ZMod p) * w t =
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)) ↔
      (b0' + ∑ t, ((X t).val : ZMod p) * w t =
        b0' + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)) := by
  constructor
  · intro h
    exact congrArg (fun x ↦ b0' + x) (add_left_cancel h)
  · intro h
    exact congrArg (fun x ↦ b0 + x) (add_left_cancel h)

theorem solution
    {p N : ℕ} {Outer : Type*} [Fintype Outer] [DecidableEq Outer]
    (compatible : Outer → Prop) [DecidablePred compatible]
    (addressX : Outer → Fin (N + 1) → Fin 5)
    (addressZ : Fin (N + 1) → Fin 5)
    (b0 b0' w0 : ZMod p) (w : Fin (N + 1) → ZMod p) :
    Finset.univ.filter (fun A : Outer ↦
      compatible A ∧
        b0 + ∑ t, (((addressX A) t).val : ZMod p) * w t =
          b0 + (2 : ZMod p)⁻¹ *
            (w0 + ∑ t,
              ((4 : ZMod p) - (addressZ t).val) * w t)) =
      Finset.univ.filter (fun A : Outer ↦
        compatible A ∧
          b0' + ∑ t, (((addressX A) t).val : ZMod p) * w t =
            b0' + (2 : ZMod p)⁻¹ *
              (w0 + ∑ t,
                ((4 : ZMod p) - (addressZ t).val) * w t)) := by
  classical
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right (fun _ ↦
    conditioned_hash_eq_independent_of_b0
      b0 b0' w0 w (addressX A) addressZ)
