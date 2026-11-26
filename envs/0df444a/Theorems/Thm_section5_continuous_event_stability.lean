-- Prove2me | Theorems.Thm_section5_continuous_event_stability
-- name    : section5_continuous_event_stability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:21.42993+00:00
-- url     : https://prove2.me/theorems/88a2a76e-97f0-5078-8742-63cc0beaf12d
-- title:
--   Stability of event energies under $L^2$ perturbations
-- statement:
--   Let $(X,\mu)$ be a measure space, let $S\subseteq X$ be measurable, and let $f,g\in L^2(\mu;\mathbb C)$ satisfy $\|f\|_2\le1$ and $\|g\|_2\le1$. Then
--
--   $$\left|\int_S|f(x)|^2\,d\mu(x)-\int_S|g(x)|^2\,d\mu(x)\right|\le2\|f-g\|_2.$$
--
--   This converts a Hilbert-space state error into a uniform bound on the change of every measurable event energy.
-- source:
--   Original measurement-stability auxiliary result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5ContinuousMeasurement.lean, lines 32–57.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
import Theorems.Thm_section5_l2_norm_sq
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory

theorem section5_continuous_event_stability {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Set α) (hs : MeasurableSet s) (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ‖hf.toLp f‖ ≤ 1) (hgn : ‖hg.toLp g‖ ≤ 1) :
    |(∫ x in s, ‖f x‖^2 ∂μ)-(∫ x in s, ‖g x‖^2 ∂μ)| ≤
      2*‖hf.toLp f-hg.toLp g‖ := by sorry
