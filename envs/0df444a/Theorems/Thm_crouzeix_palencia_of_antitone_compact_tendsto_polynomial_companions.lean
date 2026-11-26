-- Prove2me | Theorems.Thm_crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
-- name    : crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:21.562307+00:00
-- url     : https://prove2.me/theorems/c7a6f84b-455a-5f1b-b220-15d808392cd8
-- title:
--   crouzeix palencia of antitone compact tendsto polynomial companions: crouzeix palencia of antitone compact tendsto polynomial companions
-- statement:
--   If every stage of a decreasing compact exhaustion has a finite global
--   polynomial-calculus bound and uniformly contractive polynomial companions
--   converging in operator norm, then the stagewise fourth-power bootstraps and
--   sup-norm convergence give the exact Crouzeix--Palencia conclusion on the
--   intersection.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L54-L89
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L54-L89

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
set_option autoImplicit false
open Filter Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p (K n))
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p (K n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
