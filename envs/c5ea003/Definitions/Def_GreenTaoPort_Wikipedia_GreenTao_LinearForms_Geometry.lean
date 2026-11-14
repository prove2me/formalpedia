-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
-- name    : GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:05.976623+00:00
-- url     : https://prove2.me/theorems/0d7728d7-d0e2-4af1-b464-47ebd5a77a99
-- title:
--   Nonzero and independent coefficient vectors
-- statement:
--   Let $(L_q)_{q\in\kappa}$ be a family of integer affine forms with coordinate index set $\iota$. One predicate requires each coefficient vector to be nonzero. A second requires the coefficient vectors of distinct forms not to be proportional, where proportionality is expressed by vanishing of every two-by-two minor.
--
--   For the concrete Conlon–Fox–Zhao index $q$ at progression length $k$, the associated integer affine form has zero constant term and coefficient vector given by the doubled-variable coefficient construction. These definitions specify the algebraic hypotheses of the sieve's linear-forms estimate; the index types and coefficient vectors are explicit parameters.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/LinearForms/Geometry.lean#L30-L58

import Mathlib.Data.Int.Lemmas
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





end AffineForm

/-- No form in a system has the zero coefficient vector. -/
def NonzeroCoefficientVectors {κ ι : Type*}
    (forms : κ → AffineForm ι ℤ) : Prop :=
  ∀ q, (forms q).coefficient ≠ 0

/-- Distinct forms have non-proportional coefficient vectors. -/
def PairwiseIndependentCoefficients {κ ι : Type*}
    (forms : κ → AffineForm ι ℤ) : Prop :=
  Pairwise fun q r =>
    ¬IntCoefficientProportional
      (forms q).coefficient (forms r).coefficient





/-- The integer affine form underlying one CFZ index. -/
def cfzAffineForm {k : ℕ} (q : CFZFormIndex k) :
    AffineForm (CFZVariable k) ℤ where
  constant := 0
  coefficient := cfzCoefficient q













end Wikipedia.SzemeredisTheorem


