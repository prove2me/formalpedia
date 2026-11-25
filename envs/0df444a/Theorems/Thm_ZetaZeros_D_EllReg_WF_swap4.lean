-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WF_swap4
-- name    : ZetaZeros.D.EllReg.WF.swap4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:36.248389+00:00
-- url     : https://prove2.me/theorems/ba4e6c1b-388e-4118-9e64-ec60f1e0ed32
-- title:
--   WF: swap4
-- statement:
--   The WF construction uses the swap4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L315-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L315-L326

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.WF.swap4 {α : Type*} [AddCommMonoid α] (s t : Finset ℕ)
    (f : (n : ℕ) → (Fin n → Fin d) → (n' : ℕ) → (Fin n' → Fin d) → α) :
    ∑ n ∈ s, ∑ w : Fin n → Fin d, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, f n w n' w' =
      ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ n ∈ s, ∑ w : Fin n → Fin d, f n w n' w' := by sorry
