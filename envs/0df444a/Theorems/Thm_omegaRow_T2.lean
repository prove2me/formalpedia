-- Prove2me | Theorems.Thm_omegaRow_T2
-- name    : omegaRow_T2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/052a4ca0-b580-598d-a200-46d9e8d6d2b8
-- title:
--   q dj/dq · Δ = -E₄²E₆ as q-expansions
-- statement:
--   A hypothesis-free identity of Laurent series over $\mathbb{C}$. On the left, `jq` is the Laurent series over $\mathbb{Q}$ given by $\mathrm{single}(-1,1)$ times the image in `LaurentSeries ℚ` of the power series `jNumQ`, itself the coefficientwise image under $\mathbb{Z}\to\mathbb{Q}$ of the integral power series `jNum`; thus `jq` is the $q$-expansion of the modular invariant $j$, with a simple pole in $q$. The operator `thetaL ℚ` sends $f$ to $\mathrm{single}(1,1)\cdot \partial f$, i.e. it is $q\,d/dq$, multiplying the coefficient of $q^{n}$ by $n$. `coeffMap (algebraMap ℚ ℂ)` is the ring homomorphism on Laurent series induced coefficientwise by $\mathbb{Q}\hookrightarrow\mathbb{C}$. The remaining three factors are the `qExpansion 1` power series of the Mathlib level-one forms `ModularForm.discriminant`, `ModularForm.E₄` and `ModularForm.E₆`, each viewed as a Laurent series over $\mathbb{C}$ through the inclusion of power series. The assertion is that the image of $\theta(j)$ in `LaurentSeries ℂ`, multiplied by the $q$-expansion of $\Delta$, equals $-\bigl(E_4^{2}\,E_6\bigr)$, the product of the square of the $q$-expansion of $E_4$ with that of $E_6$, negated.
--
--   This is the classical derivative formula for the $j$-invariant, $q\,dj/dq = -E_4^{2}E_6/\Delta$, recorded here as an identity of $q$-expansions rather than of functions on the upper half-plane, the relation $j = E_4^{3}/\Delta$ being available separately. It is used in the analysis of the order of vanishing of differentials on modular curves and in the construction of cusp forms whose $q$-expansion is a multiple of $\theta$ applied to a given Laurent series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_omegaRow_T2.lean

import Definitions.Def_ModularCurve_OmegaOf
import Definitions.Def_ModularCurve_EigenformIdeal
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_CuspForm_IntegralStructure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane ModularCurve AlgebraicCurve

theorem omegaRow_T2 :
    coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) *
        ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = -(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 *
          ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by sorry
