-- Prove2me | solution 1 for QuadraticFormsNumberFields.anisotropic_iff_of_isometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:54:41.242042+00:00
-- url     : https://prove2.me/submissions/a163d0b8-1d1c-4a9a-b609-616d930439ae

-- Sol generated from Algebra/QuadraticFormsNumberFields.lean
import Mathlib
import Definitions.Def_Algebra_QuadraticFormsNumberFields
/-
# Quadratic forms over number fields: local-global infrastructure

This file develops kernel-checked algebraic consequences needed by a future full
place-theoretic Hasse--Minkowski theorem.  It uses Mathlib's `QuadraticForm`,
`QuadraticMap.Anisotropic`, isometric equivalences, and scalar extension.

The actual construction of all completions of a number field and the arithmetic
reciprocity theorem are not currently part of Mathlib.  The results here therefore
establish unconditional invariance and scalar-extension foundations on which a
future place-theoretic Hasse--Minkowski theorem can be built.
-/


open scoped TensorProduct

open QuadraticFormsNumberFields

open QuadraticMap

noncomputable section


variable {K L V W : Type*}


variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
















open QuadraticFormsNumberFields in
theorem solution    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (e : Q.IsometryEquiv Q') : Q.Anisotropic ↔ Q'.Anisotropic := by
  let e' := e.toLinearEquiv
  have he : ∀ x, Q' (e' x) = Q x := fun x => e.2 x
  constructor
  · intro hQ x hx
    have h1 : Q (e'.symm x) = Q' x :=
      (he (e'.symm x)).symm.trans (by rw [e'.apply_symm_apply])
    rw [hx] at h1
    have h2 : e'.symm x = 0 := hQ _ h1
    exact e'.symm.injective (by simpa using h2)
  · intro hQ' x hx
    have h1 : Q' (e' x) = Q x := he x
    rw [hx] at h1
    have h2 : e' x = 0 := hQ' _ h1
    exact e'.injective (by simpa using h2)
