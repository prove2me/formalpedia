-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_3_3
-- name    : ZeroFreeRRG.Hardcore.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:35:42.438909+00:00
-- url     : https://prove2.me/theorems/b6a6cabb-d78e-4d57-bd64-42da5162dd9d
-- title:
--   Lemma 3.3 — mean-value inequality ‖h‖²_K ≤ C_{K,L} ∫_L |h|² dA for holomorphic h
-- statement:
--   Let $D\subseteq\mathbb C$ be open and connected, and let $K,L$ be compact with $K\subset\operatorname{int}(L)\subset L\subset D$. There is a constant $C_{K,L}>0$ such that every $h$ holomorphic on $D$ satisfies
--   $$\|h\|_K^2\le C_{K,L}\int_L|h(z)|^2\,dA(z),$$
--   where $dA$ is planar Lebesgue measure. This converts the second-moment bound (B5) into tightness in $H(D)$ (Lemma 3.5).
--
--   Differences from the source:
--   - encoding: ‖h‖_K² = sup_{z∈K} |h(z)|² → |h(z)|² ≤ C ∫_L |h|² for every z ∈ K; reason: a bound on every value is a bound on the supremum
--   - encoding: dA, planar area measure → volume on ℂ (Lebesgue measure transported from ℝ²); reason: same measure
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 19, Lemma 3.3

import Mathlib

open MeasureTheory

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 3.3** (mean-value inequality; p. 19). Let `D ⊆ ℂ` be open and connected and let `K`,
`L` be compact with `K ⊆ int(L) ⊆ L ⊆ D`. There is `C_{K,L} > 0` such that every `h` holomorphic on
`D` satisfies `‖h‖_K² ≤ C_{K,L} ∫_L |h(z)|² dA(z)` (`dA` = planar Lebesgue measure). The supremum
bound is written pointwise for every `z ∈ K`. -/
theorem lemma_3_3 (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (K L : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L) (hLD : L ⊆ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℂ → ℂ, DifferentiableOn ℂ h D →
      ∀ z ∈ K, ‖h z‖ ^ 2 ≤ C * ∫ w in L, ‖h w‖ ^ 2 := by sorry

end ZeroFreeRRG.Hardcore
