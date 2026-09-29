-- Prove2me | solution 1 for FourierFA.dft_transl
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:10:50.046597+00:00
-- url     : https://prove2.me/submissions/0295ff36-d692-4cfa-a5da-ab3eb20b2da4

-- Sol generated from Shared/FourierExtremals.lean
import Mathlib
import Definitions.Def_Shared_FourierExtremals
import Definitions.Def_Shared_FourierFiniteAbelian
import Definitions.Def_Shared_FourierSubgroupDuality
/-
# Symmetries of the discrete Fourier transform and extremals of the uncertainty principle

Building on `Catalog.Shared.FourierFiniteAbelian` and `Catalog.Shared.FourierSubgroupDuality`,
this file records how the DFT interacts with the three basic symmetries of `G → ℂ`
(scaling, translation, modulation) and deduces a large family of functions attaining
equality in the Donoho–Stark uncertainty principle `|supp f| * |supp f̂| ≥ |G|`.

Main results:

* `FourierFA.dft_transl` : `(f(· - a))^(ψ) = conj (ψ a) · f̂(ψ)` (translation ↦ modulation).
* `FourierFA.dft_modul` : `(χ · f)^(ψ) = f̂(ψ - χ)` (modulation ↦ translation in the dual).
* `FourierFA.IsExtremal` : the property `|supp f| * |supp f̂| = |G|`.
* `FourierFA.IsExtremal.smul`, `.transl`, `.modul` : the extremal functions form a set invariant
  under the three symmetries.
* `FourierFA.isExtremal_coset_modulation` : every function of the form
  `x ↦ c · χ x · 1_H (x - a)` (with `c ≠ 0`, `H` a subgroup) is extremal.
-/


open Finset ComplexConjugate

open FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The three symmetries -/





/-! ## Supports under the symmetries -/






/-! ## Extremal functions -/









open FourierFA in
omit [DecidableEq G] in
theorem solution(a : G) (f : G → ℂ) (ψ : AddChar G ℂ) :
    dft (transl a f) ψ = conj (ψ a) * dft f ψ := by
  rw [dft, dft, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight a) (fun x => conj (ψ x) * transl a f x)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hy : (Equiv.addRight a) y = y + a := rfl
  rw [hy]
  have h1 : transl a f (y + a) = f y := by
    rw [transl, add_sub_cancel_right]
  have h2 : conj (ψ (y + a)) = conj (ψ y) * conj (ψ a) := by
    rw [ψ.map_add_eq_mul, map_mul]
  rw [h1, h2]
  ring
