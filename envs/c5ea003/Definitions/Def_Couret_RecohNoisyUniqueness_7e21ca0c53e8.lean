-- Prove2me | Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
-- name    : Couret_RecohNoisyUniqueness_7e21ca0c53e8
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:19.934569+00:00
-- url     : https://prove2.me/theorems/2bab4ba6-1ffe-4c83-a4a8-4e602520cf5a
-- title:
--   An exact rational tolerance filter on finite candidates
-- statement:
--   Let $X$ have decidable equality, $I$ be any finite coordinate type, and $C\subseteq X$ be a supplied finite candidate set. Let $p:X\to I\to\mathbb Q^2$ give predicted complex coordinates and $o:I\to\mathbb Q^2$ observed coordinates. For rational radius $r$, the decoder is $$D(C,p,o,r)=\{S\in C:r\ge0\text{ and }\forall i,\ d_{\mathbb Q}(o_i,p(S,i))^2\le r^2\},$$ where squared distance is the sum of the two rational coordinate-difference squares. It performs only rational comparisons. Negative radii reject all candidates; for an empty coordinate type, a nonnegative radius accepts every supplied candidate. Accuracy, separation, true-candidate membership and error budgets are hypotheses of separate correctness results, not assumptions or consequences of this definition alone.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisyUniqueness.lean; source file SHA-256 6052faa2e2efbc2d3e68381058002e13b4872e2433fd587269e83b1de0f67f8c

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
Noise tolerance with explicit prediction error.  The executable decoder
below compares rational squared distances.  Its correctness theorem relates
those comparisons to the complex readings, accounting separately for the
measurement error, the prediction error, and the acceptance radius.

The candidate set is supplied explicitly.  Completeness requires the true
support to occur in that set; this module makes no ambient enumeration claim.
-/

namespace Couret.STROBO2TORS









/-- A finite, executable decoder.  Negative radii reject every candidate.
No equality or order comparison of real or complex numbers is performed. -/
def recohRationalNoisyDecoder {X I : Type*} [DecidableEq X] [Fintype I]
    (candidates : Finset X) (predicted : X → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) : Finset X :=
  candidates.filter fun S => 0 ≤ radius ∧
    ∀ i, recohRationalSquaredDistance (observed i) (predicted S i) ≤ radius ^ 2















end Couret.STROBO2TORS


