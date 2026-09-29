-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_SPBAlgebra
-- name    : Bridges_TropicalAlgebra_SPBAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:26.759245+00:00
-- url     : https://prove2.me/theorems/622b5fd5-0a5f-4845-8037-d0ba30a19d1a
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_SPBAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.SPBAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/SPBAlgebra.lean by skeleton subtraction
import Mathlib

/-! # SPB Algebraic Structure

The Stereographic Pythagorean Bridge operation spb(x,y) = (x+y)/(1+xy)
has rich algebraic properties. This file formalizes the group-like structure
and its connections to trigonometry, hyperbolic geometry, and tropical limits.

## Main Results

- `spb_assoc`: SPB is associative (when denominators are nonzero)
- `spb_comm`: SPB is commutative
- `spb_zero_left/right`: 0 is the identity
- `spb_neg_inverse`: -x is the inverse of x
- `spb_tanh_add`: SPB encodes the tanh addition formula
- `spb_self_double`: spb(x,x) = 2x/(1+x²)
- `spb_bounded`: |spb(x,y)| < 1 when |x| < 1 and |y| < 1
-/

noncomputable section

/-- The SPB operation. -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 + x * y)







/-
SPB is associative when denominators are nonzero.
-/

/-
SPB is bounded: if |x| < 1 and |y| < 1, then |spb(x,y)| < 1.
-/

/-
The denominator 1+xy > 0 when |x| < 1 and |y| < 1.
-/


/-
SPB encodes the tanh addition formula:
    spb(tanh(a), tanh(b)) = tanh(a + b).
    Here we prove the self-doubling case: spb(tanh(a), tanh(a)) = tanh(2a).
    This is the Wick-rotated version of the tangent double-angle formula.
-/


end


