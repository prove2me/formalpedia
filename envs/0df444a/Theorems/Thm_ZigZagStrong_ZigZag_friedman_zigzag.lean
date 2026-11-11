-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_friedman_zigzag
-- name    : ZigZagStrong.ZigZag.friedman_zigzag
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:03.121038+00:00
-- url     : https://prove2.me/theorems/50780eba-0d62-4fc9-8199-95b5190ff067
-- title:
--   Theorem 1.2 — strong convergence and sharp spectral edges of zig-zag products
-- statement:
--   Fix a good vertex-transitive $c$-regular gadget $H$ on $d$ ports under Section 3.1's standing hypotheses. In the independent matching model, and in the independent permutation model when $d=2r$, every finite nonempty realization has trivial spectrum $\operatorname{spec}(A_H^2)$ and $\operatorname{spec}(A_HF_SA_H)$ respectively. In each model,
--   $$d_H(\operatorname{spec}(Z|_{\mathcal H_{\rm new}}),\operatorname{spec}(A_{X_H}))\longrightarrow0,\qquad\|Z|_{\mathcal H_{\rm new}}\|\longrightarrow\Lambda_H$$
--   in probability. In addition, in the permutation model there are $C_H>0$ and $n_H$, depending only on $H$, such that for every $n\ge n_H$ and every $\varepsilon>0$,
--   $$\Pr[\|Z|_{\mathcal H_{\rm new}}\|\ge\Lambda_H+\varepsilon]\le\frac{C_H}{n\varepsilon^9}.$$
--   This is the conjunction of all three headline clauses, including both directed spectral approximations and the sharp determinant-defined edge.
--
--   Differences from the source:
--   - encoding: Finite vertex sets and real self-adjoint spectra → Fin-indexed vertex sets and complex operator spectra with their full Hausdorff distance; reason: Finite sets are transported along bijections; real-axis inclusion preserves distances and spectra.
--   - encoding: The limit n tends to infinity, along even n for matchings → Sizes n+2 for permutations/involutions and 2*(n+1) for matchings; reason: Removing finitely many undefined zero-dimensional spectral cases changes no asymptotic statement and includes every sufficiently large admissible size.
--   - reading: Informal Theorem 1.2 says H as above and suppresses the degeneracy restriction → The precise Section 3.1 scope: Good H, d>=3 and c>=2; reason: Theorem 1.2 explicitly points to Theorem 3.5, whose standing hypotheses import CCM24 Theorem 5.2 and Definition 5.1; no arbitrary narrower gadget class is chosen.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Theorem 1.2, p. 4.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem friedman_zigzag {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c) (hg : Good H) :
  ((∀ n : ℕ, 0 < n → ∀ τ : Fin d → Matching n,
      spectrum ℂ (trivialAdj H (Equiv.refl _) (fun i => (τ i).val)) =
        spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (H.mat ^ 2))) ∧
    ProbConverges (fun n => finiteLaw (Ω := Fin d → Matching (2*(n+1))))
      (fun _ τ => spectrumDistance (matchingNew H τ) (matchingLimit H)) 0 ∧
    ProbConverges (fun n => finiteLaw (Ω := Fin d → Matching (2*(n+1))))
      (fun _ τ => ‖matchingNew H τ‖) (sharpEdge H)) ∧
  (∀ r : ℕ, ∀ h : d = 2*r, let H' := h ▸ H;
    (∀ n : ℕ, 0 < n → ∀ σ : Fin r → Equiv.Perm (Fin n),
      spectrum ℂ (trivialAdj H' Fin.revPerm (permutationPorts σ)) =
        spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ)
          (H'.mat * (∑ i, elementary i (Fin.revPerm i)) * H'.mat))) ∧
    ProbConverges (fun n => finiteLaw (Ω := Fin r → Equiv.Perm (Fin (n+2))))
      (fun _ σ => spectrumDistance (permutationNew H' σ) (permutationLimit H')) 0 ∧
    ProbConverges (fun n => finiteLaw (Ω := Fin r → Equiv.Perm (Fin (n+2))))
      (fun _ σ => ‖permutationNew H' σ‖) (sharpEdge H) ∧
    (∃ C_H : ℝ, 0 < C_H ∧ ∃ n_H : ℕ, ∀ n : ℕ, n_H ≤ n → ∀ ε : ℝ, 0 < ε →
      StrongConv.uniformProb (fun σ : Fin r → Equiv.Perm (Fin n) =>
        sharpEdge H + ε ≤ ‖permutationNew H' σ‖) ≤ C_H / ((n : ℝ)*ε^9))) := by sorry

end ZigZagStrong.ZigZag
