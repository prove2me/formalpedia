-- Prove2me | Definitions.Def_Couret_StroboHomometry_90864170804d
-- name    : Couret_StroboHomometry_90864170804d
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:39.031461+00:00
-- url     : https://prove2.me/theorems/1748196b-7913-4220-a089-8517c20ec701
-- title:
--   Unnormalized difference autocorrelation and character probes
-- statement:
--   For an abelian group $G$ and finite support $S$, define $$D_S(z)=\sum_{x\in S}\sum_{y\in S}1_{x-y=z},\qquad P_S(\chi)=\sum_{x\in S}\chi(x),$$ where $\chi$ is a complex additive character. The difference count retains ordered multiplicities and all diagonal pairs; the probe has no normalization. These raw definitions do not require a finite ambient group or cardinality three for the support. They provide the observable vocabulary for later finite Fourier implications; the bundle itself does not assert their converse or an ambient classification.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/41a2ef6f6ae6f6a26b3d630d365ad404fd97fe42/research/strobo-2tors-2026-10-12/lean/StroboHomometry.lean; source file SHA-256 d425a917138d22db0e9336b5a0dc3446107f7fd9eaaac85386bc9bdfb4cba274

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Classical Fourier implication, made explicit for the existing STROBO observable:
equal labelled ordered convolution squares imply equal difference multiplicities.
No converse and no novelty claim. See Lev (2004), section 3, Problem 2, p. 5,
and Riley Casper's observation of 2026-10-15.
-/

open scoped BigOperators ComplexConjugate

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Ordered difference counts, including the diagonal. No normalization. -/
def differenceAutocorrelation (S : Finset G) (z : G) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ S, if x - y = z then 1 else 0

/-- Unnormalized character sum of the indicator of a finite support. -/
noncomputable def supportProbe (S : Finset G) (χ : AddChar G ℂ) : ℂ := ∑ x ∈ S, χ x



section Finite
variable [Fintype G]





















end Finite



end Couret.STROBO2TORS


