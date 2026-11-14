-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_latent_mixture_density_support
-- name    : ZeroFreeRRG.Hardcore.latent_mixture_density_support
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:38:55.62764+00:00
-- url     : https://prove2.me/theorems/3d91ff0d-7f3b-44a7-9249-61da01d4b4db
-- title:
--   Support of finite latent-mixture densities
-- statement:
--   For nonnegative finite families $A_i,u_i,v_i$, put $S=\sum_i A_i$, $L=\sum_i A_i u_i$, $R=\sum_i A_i v_i$, and $T=\sum_i A_i u_i v_i$. Then $T$ and $LR/S$ are nonnegative, and $LR/S=0$ implies $T=0$, using the convention $0/0=0$. This verifies the absolute-continuity support condition for the latent-mixture relative-entropy argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib
open scoped BigOperators

namespace ZeroFreeRRG.Hardcore
theorem latent_mixture_density_support {ι : Type} [Fintype ι] (A u v : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    let S := ∑ i, A i
    let L := ∑ i, A i*u i
    let R := ∑ i, A i*v i
    let T := ∑ i, A i*u i*v i
    0 ≤ T ∧ 0 ≤ L*R/S ∧ (L*R/S = 0 → T=0) := by sorry
end ZeroFreeRRG.Hardcore
