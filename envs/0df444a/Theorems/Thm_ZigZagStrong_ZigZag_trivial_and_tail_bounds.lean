-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_trivial_and_tail_bounds
-- name    : ZigZagStrong.ZigZag.trivial_and_tail_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:27.026199+00:00
-- url     : https://prove2.me/theorems/749be447-00cb-44be-acae-0f7d96968c7f
-- title:
--   Theorem 3.5 — trivial spectra and all three model tail bounds
-- statement:
--   Let $H$ be a good vertex-transitive $c$-regular gadget, with the standing sharp-edge assumptions. For $d=2r$, the permutation model has trivial spectrum $\operatorname{spec}(A_HF_SA_H)$ and
--   $$\Pr[\lambda_{\rm new}\ge\Lambda_H+\varepsilon]\le\frac{C_H}{n\varepsilon^9}$$
--   for every $\varepsilon>0$ and all sufficiently large $n$, with $C_H>0$ and the initial-size threshold depending only on $H$. For the matching and involution models on $d$ ports, the trivial spectrum is $\operatorname{spec}(A_H^2)$ and, for every $\varepsilon>0$,
--   $$\Pr[\lambda_{\rm new}\ge\Lambda_H+\varepsilon]\longrightarrow0.$$
--   Both numbered clauses, and both models in the second clause, are included.
--
--   Differences from the source:
--   - encoding: Finite vertex sets and real self-adjoint spectra → Fin-indexed vertex sets and complex operator spectra with their full Hausdorff distance; reason: Finite sets are transported along bijections; real-axis inclusion preserves distances and spectra.
--   - encoding: The limit n tends to infinity, along even n for matchings → Sizes n+2 for permutations/involutions and 2*(n+1) for matchings; reason: Removing finitely many undefined zero-dimensional spectral cases changes no asymptotic statement and includes every sufficiently large admissible size.
--   - encoding: Good H as specified by the standing hypotheses in Section 3.1 → Explicit Good H, d>=3 and c>=2, with H-only constants before n and epsilon; reason: The imported source Theorem 5.2 states these size and degree assumptions; the bounds keep all allowed gadgets and all positive tolerances.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Theorem 3.5, p. 11 (continues on p. 12).

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem trivial_and_tail_bounds  :
  (∀ r c : ℕ, ∀ H : Gadget (2*r) c, 3 ≤ 2*r → 2 ≤ c → Good H →
    (∀ n : ℕ, 0 < n → ∀ σ : Fin r → Equiv.Perm (Fin n),
      spectrum ℂ (trivialAdj H Fin.revPerm (permutationPorts σ)) =
        spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ)
          (H.mat * (∑ i, elementary i (Fin.revPerm i)) * H.mat))) ∧
    (∃ C_H : ℝ, 0 < C_H ∧ ∃ n_H : ℕ, ∀ n : ℕ, n_H ≤ n → ∀ ε : ℝ, 0 < ε →
      StrongConv.uniformProb (fun σ : Fin r → Equiv.Perm (Fin n) =>
        sharpEdge H + ε ≤ ‖permutationNew H σ‖) ≤ C_H / ((n : ℝ)*ε^9))) ∧
  (∀ d c : ℕ, ∀ H : Gadget d c, 3 ≤ d → 2 ≤ c → Good H →
    (∀ n : ℕ, 0 < n → ∀ τ : Fin d → Involution n,
      spectrum ℂ (trivialAdj H (Equiv.refl _) (fun i => (τ i).val)) =
        spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (H.mat ^ 2))) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      StrongConv.uniformProb (fun τ : Fin d → Matching (2*(n+1)) =>
        sharpEdge H + ε ≤ ‖matchingNew H τ‖)) atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      StrongConv.uniformProb (fun τ : Fin d → Involution (n+2) =>
        sharpEdge H + ε ≤ ‖involutionNew H τ‖)) atTop (𝓝 0))) := by sorry

end ZigZagStrong.ZigZag
