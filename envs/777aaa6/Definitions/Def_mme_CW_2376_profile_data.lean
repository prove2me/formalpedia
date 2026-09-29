-- Prove2me | Definitions.Def_mme_CW_2376_profile_data
-- name    : mme_CW_2376_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T15:49:59.367051+00:00
-- url     : https://prove2.me/theorems/7801300e-9e17-43bd-af94-1985e8b5f81c
-- title:
--   Exact finite profile data for the CW 2.376 extraction
-- statement:
--   At scale $m$, set $N=3{,}000{,}000m$ and use the exact joint orbit multiplicities $(699,37518,307638,616627)m$. The six $\langle1,1,12\rangle$ constituents and three $\langle1,1,38\rangle$ constituents combine to a square matrix-multiplication factor of side $12^{75036m}38^{307638m}$, while the three coupled classes combine to the $616627m$-th power of the cyclic coupled tensor. The module also records the marginal-entropy count base, the free-coupled numerator base, and the explicit positive loss envelope $r_m=(\sqrt{\sqrt{m+1}})^{-1}$. The latter tends to zero more slowly than both the explicit Behrend loss $O(m^{-1/2})$ and the polynomial multinomial loss $O(\log(m)/m)$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (11), equations (12)--(13), and the auxiliary equation on journal pp. 265--269; explicit Salem--Spencer/Behrend estimate as formalized by Behrend.roth_lower_bound.

import Definitions.Def_mme_CW_auxiliary_RHS_coupled
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_rank
import Mathlib.Data.Real.Sqrt

/-!
# Exact finite profile data for the Coppersmith--Winograd 2.376 extraction

At scale `m`, put `N = 3000000 * m`.  The exact joint multiplicities are
`(699, 37518, 307638, 616627) * m`.  The six rectangular constituents of
the second orbit and the three rectangular constituents of the third orbit
combine to a square matrix-multiplication tensor of side

`12^(75036*m) * 38^(307638*m)`.

The remaining three coupled constituents combine to the `616627*m`-th
Kronecker power of the cyclic symmetrization of the coupled `(1,1,2)` block.
-/

namespace MME

universe u

/-- The common side of the elementary matrix-multiplication factor in one
surviving exact-profile block at scale `m`. -/
def cw2376ProfileSide (m : ℕ) : ℕ :=
  12 ^ (75036 * m) * 38 ^ (307638 * m)

/-- The tensor carried by one surviving exact-profile block, before a finite
witness is substituted for the coupled constituent. -/
noncomputable def cw2376ProfileCore
    (K : Type u) [Field K] (m : ℕ) : TensorObj K 3 :=
  TensorObj.kron
    (MMObj K (cw2376ProfileSide m) (cw2376ProfileSide m)
      (cw2376ProfileSide m))
    ((cyclicSymmetrization (coupledObj K 6)).kronPow (616627 * m))

/-- The exponential base supplied by the number of disjoint surviving
five-grade blocks.  It is the reciprocal of the five marginal entropy
denominator in equation (13). -/
noncomputable def cw2376ProfileCountBase : ℝ :=
  1 /
    ((2 * cw2376_a + 2 * cw2376_b + cw2376_c) ^
        (2 * cw2376_a + 2 * cw2376_b + cw2376_c) *
      (2 * cw2376_b + 2 * cw2376_d) ^
        (2 * cw2376_b + 2 * cw2376_d) *
      (2 * cw2376_c + cw2376_d) ^
        (2 * cw2376_c + cw2376_d) *
      (2 * cw2376_b) ^ (2 * cw2376_b) *
      cw2376_a ^ cw2376_a)

/-- The per-square-factor tau-weight contributed by the six rectangular
blocks, the three `(0,2,2)` blocks, and a free cyclic-coupled base `Vc`. -/
noncomputable def cw2376ProfileNumeratorBase (tau Vc : ℝ) : ℝ :=
  (12 : ℝ) ^ (6 * tau * cw2376_b) *
    (38 : ℝ) ^ (3 * tau * cw2376_c) *
    Vc ^ cw2376_d

/-- A slack explicit per-root loss envelope for the finite profile extraction.
The Behrend hashing loss is `O(m⁻¹²)` and the multinomial losses are
`O(log m / m)`, so the slower-decaying positive envelope `m⁻¹⁴` absorbs
both for all sufficiently large `m`. -/
noncomputable def cw2376ProfileRate (m : ℕ) : ℝ :=
  (Real.sqrt (Real.sqrt ((m : ℝ) + 1)))⁻¹

end MME


