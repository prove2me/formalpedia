-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_integrated_relative_entropy_nonnegative
-- name    : ZeroFreeRRG.Hardcore.integrated_relative_entropy_nonnegative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:37:43.243707+00:00
-- url     : https://prove2.me/theorems/ddc436a4-fc57-49c5-8696-f9f11860be5b
-- title:
--   Integrated relative-entropy inequality with zero densities
-- statement:
--   Let $p$ and $q$ be integrable nonnegative densities of equal total mass. Suppose $p=0$ almost everywhere on the zero set of $q$, and both $p\log p$ and $p\log q$ are integrable. Then $\int p\log q\le\int p\log p$. The zero-density case is included. This is the nonnegativity of relative entropy used in the entropy-increment argument for Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem integrated_relative_entropy_nonnegative {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (p q : Ω → ℝ)
    (hpos : ∀ᵐ ω ∂μ, 0 ≤ p ω ∧ 0 ≤ q ω ∧ (q ω = 0 → p ω = 0))
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpp : Integrable (fun ω => p ω * Real.log (p ω)) μ)
    (hpq : Integrable (fun ω => p ω * Real.log (q ω)) μ)
    (hmass : (∫ ω, p ω ∂μ) = ∫ ω, q ω ∂μ) :
    (∫ ω, p ω * Real.log (q ω) ∂μ) ≤ ∫ ω, p ω * Real.log (p ω) ∂μ := by sorry
end ZeroFreeRRG.Hardcore
