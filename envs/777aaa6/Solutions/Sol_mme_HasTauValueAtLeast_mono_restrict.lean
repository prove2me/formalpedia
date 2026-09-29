-- Prove2me | solution 1 for mme_HasTauValueAtLeast_mono_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:03:09.450719+00:00
-- url     : https://prove2.me/submissions/33356640-ad4e-478a-98dc-ca2de641e39b

import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_restrict_kronPow

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    {X Y : TensorObj K 3} {tau V : ℝ}
    (hXY : TensorObj.Restrict X Y)
    (hX : HasTauValueAtLeast X tau V) :
    HasTauValueAtLeast Y tau V := by
  refine ⟨hX.1, ?_⟩
  intro epsilon hepsilon
  exact (hX.2 epsilon hepsilon).mono (fun N hN => by
    obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hN
    refine ⟨k, a, b, c, ?_, hweight⟩
    exact TensorObj.Restrict.trans hrestrict
      (mme_restrict_kronPow hXY N))
