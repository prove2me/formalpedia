-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_conditional_entropy_log_identity
-- name    : ZeroFreeRRG.Hardcore.conditional_entropy_log_identity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:44:43.49008+00:00
-- url     : https://prove2.me/theorems/cd51a13c-534d-441e-bb40-75e35affb436
-- title:
--   Conditional entropy logarithm identity with zero densities
-- statement:
--   For real $S,L,R,T$, suppose each of $S=0$, $L=0$, or $R=0$ forces $T=0$. Then $T\log(LR/S)=T\log L+T\log R-T\log S$, using $\log0=0$. This handles the zero-density cases in the conditional relative-entropy calculation underlying Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib

namespace ZeroFreeRRG.Hardcore
theorem conditional_entropy_log_identity (S L R T : ℝ)
    (hS : S=0 → T=0) (hL : L=0 → T=0) (hR : R=0 → T=0) :
    T * Real.log (L*R/S) = T*Real.log L + T*Real.log R - T*Real.log S := by sorry
end ZeroFreeRRG.Hardcore
