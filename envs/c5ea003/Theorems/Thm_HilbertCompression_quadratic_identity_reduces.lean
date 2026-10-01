-- Prove2me | Theorems.Thm_HilbertCompression_quadratic_identity_reduces
-- name    : HilbertCompression.quadratic_identity_reduces
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:30:05.621395+00:00
-- url     : https://prove2.me/theorems/e32bbdf5-7706-4c26-a05f-3f54d4d2866b
-- title:
--   Rigidez da compressão pela igualdade da soma de quadrados
-- statement:
--   Let $H$ be a complete complex Hilbert space, let $X,Y\in\mathcal B(H)$ be bounded self-adjoint operators, and let $P\in\mathcal B(H)$ be an orthogonal projection. If
--
--   $$
--   P(X^2+Y^2)P=(PXP)^2+(PYP)^2,
--   $$
--
--   then
--
--   $$
--   PX=XP,\qquad PY=YP.
--   $$
--
--   The criterion shows that the projected subspace simultaneously reduces two operators from a single quadratic identity. It holds in arbitrary dimension, including the zero space, and requires neither positivity nor commutativity of $X,Y$.
--
--   This is a derived algebraic lemma for CUHK-Shenzhen Problem 2. The source's question for every continuous strictly convex function remains separate.
-- source:
--   Derived algebraic compression criterion supporting CUHK-Shenzhen AI Math Problems, Problem 2, https://rybindmitry.github.io/problems/2.html, displayed compression equality and reduction question. The source poses the general strictly convex problem; this supporting quadratic criterion is not stated separately there.

import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false

theorem HilbertCompression.quadratic_identity_reduces
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X Y P : H →L[ℂ] H)
    (hX : star X = X) (hY : star Y = Y)
    (hP : star P = P) (hPP : P * P = P)
    (hquadrado : P * (X * X + Y * Y) * P =
      (P * X * P) * (P * X * P) + (P * Y * P) * (P * Y * P)) :
    P * X = X * P ∧ P * Y = Y * P := by sorry
