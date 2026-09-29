-- Prove2me | solution 1 for emlNeuron_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:49:41.572342+00:00
-- url     : https://prove2.me/submissions/7ac9af11-7794-410c-96a2-e44d78c8ba7a

import Mathlib
import Definitions.Def_EML_SPBExtended_EMLNeuralNetworks
theorem solution (w₁ b₁ w₂ b₂ x : ℝ) (h : w₂ * x + b₂ ≠ 0) :
    HasDerivAt (fun x' => emlNeuron w₁ b₁ w₂ b₂ x')
      (w₁ * Real.exp (w₁ * x + b₁) - w₂ / (w₂ * x + b₂)) x := by
  -- chain rule on `exp (w₁ x + b₁)` and `log (w₂ x + b₂)`
  have h1 : HasDerivAt (fun x => w₁ * x + b₁) w₁ x := by
    simpa using ((hasDerivAt_id x).const_mul w₁).add_const b₁
  have h2 : HasDerivAt (fun x => w₂ * x + b₂) w₂ x := by
    simpa using ((hasDerivAt_id x).const_mul w₂).add_const b₂
  have hd := h1.exp.sub (h2.log h)
  show HasDerivAt (fun x' => Real.exp (w₁ * x' + b₁) - Real.log (w₂ * x' + b₂)) _ x
  convert hd using 1
  ring
