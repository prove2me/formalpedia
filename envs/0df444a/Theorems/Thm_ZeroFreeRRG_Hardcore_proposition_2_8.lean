-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_proposition_2_8
-- name    : ZeroFreeRRG.Hardcore.proposition_2_8
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:16:56.884772+00:00
-- url     : https://prove2.me/theorems/85f86f24-60f5-4d6b-b33c-46fce53d9877
-- title:
--   Identity theorem for holomorphic functions
-- statement:
--   Let $D\subseteq\mathbb C$ be an open connected region, and let $f$ and $g$ be holomorphic on $D$. Suppose $S\subseteq D$ has an accumulation point $z_0\in D$, and $f=g$ on $S$. Then $f=g$ on all of $D$. The accumulation-point condition means that $z_0$ lies in the closure of $S\setminus\{z_0\}$.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Proposition 2.8, printed p. 17.

import Mathlib
open Set

namespace ZeroFreeRRG.Hardcore
theorem proposition_2_8 (D S : Set ℂ) (f g : ℂ → ℂ) (z₀ : ℂ)
    (hopen : IsOpen D) (hconnected : IsConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hSD : S ⊆ D) (hz : z₀ ∈ D) (hacc : z₀ ∈ closure (S \ {z₀}))
    (heq : ∀ z ∈ S, f z = g z) : EqOn f g D := by sorry
end ZeroFreeRRG.Hardcore
