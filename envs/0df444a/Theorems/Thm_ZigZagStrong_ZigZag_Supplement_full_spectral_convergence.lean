-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_Supplement_full_spectral_convergence
-- name    : ZigZagStrong.ZigZag.Supplement.full_spectral_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:52.583239+00:00
-- url     : https://prove2.me/theorems/1bfef5bd-7a57-4cff-aa2e-1f723365430f
-- title:
--   Theorem 3.6 — full spectrum of random zig-zag products converges to the union with the trivial spectrum
-- statement:
--   Let $H$ be a good vertex-transitive $c$-regular gadget as in Theorem 3.5 (on $d=2r$ ports for the permutation model, $d\ge3$, $c\ge2$), with adjacency matrix $A_H$, and let $A_{G_n\,z\,H}$ be the adjacency operator of the zig-zag product of the random graph $G_n$ with $H$ (the whole operator, trivial and new parts together).
--
--   1. In the permutation model, with port-flip matrix $F_S$,
--   $$d_H\Big(\operatorname{spec}(A_{G_n z H}),\ \operatorname{spec}(A_HF_SA_H)\cup\operatorname{spec}(A_{T_{2r} z H})\Big)\xrightarrow[n\to\infty]{P}0.$$
--   2. In the matching model and in the involution model,
--   $$d_H\Big(\operatorname{spec}(A_{G_n z H}),\ \operatorname{spec}(A_H^2)\cup\operatorname{spec}(A_{T_r z H})\Big)\xrightarrow[n\to\infty]{P}0.$$
--
--   Here $d_H$ is the Hausdorff distance and $T_{2r}\,z\,H$, $T_r\,z\,H$ are the regular zig-zag products of the free group $F_r$ and of $\mathbb Z_2^{*r}$. Unlike the goal theorem, which treats the trivial and new spectra separately, this controls the entire spectrum.
--
--   Differences from the source:
--   - encoding: finite vertex sets and real self-adjoint spectra → Fin-indexed vertex sets and complex operator spectra (zig-zag operator of Eq. (6) with permutation-matrix ports) with their Hausdorff distance; reason: as in the base mission: finite sets are transported along bijections; real-axis inclusion preserves distances and spectra
--   - encoding: the limit n → ∞, along even n for matchings → sizes n+2 for permutations and involutions and 2(n+1) for matchings; reason: as in the base goal: dropping finitely many small sizes changes no limit, every sufficiently large admissible size is included
--   - reading: H as in Theorem 3.5 → the base mission's moderated reading: Gadget d c with 3 ≤ d, 2 ≤ c and Good H (which includes vertex transitivity), d = 2r and port flip Fin.revPerm in the permutation clause; reason: identical to the published trivial_and_tail_bounds (Theorem 3.5); no hypothesis is dropped or added
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Theorem 3.6, p. 12 (proved on p. 15).

import Definitions.Def_ZigZagStrong_ZigZag_Models

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open Filter MeasureTheory
open scoped BigOperators Topology

theorem full_spectral_convergence :
  (∀ r c : ℕ, ∀ H : Gadget (2*r) c, 3 ≤ 2*r → 2 ≤ c → Good H →
    ProbConverges (fun n => finiteLaw (Ω := Fin r → Equiv.Perm (Fin (n+2))))
      (fun _ σ => Metric.hausdorffDist
        (spectrum ℂ (zigzag H Fin.revPerm (fun i => StrongConv.permOp (permutationPorts σ i))))
        (spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ)
            (H.mat * (∑ i, elementary i (Fin.revPerm i)) * H.mat)) ∪
          spectrum ℂ (permutationLimit H))) 0) ∧
  (∀ d c : ℕ, ∀ H : Gadget d c, 3 ≤ d → 2 ≤ c → Good H →
    ProbConverges (fun n => finiteLaw (Ω := Fin d → Matching (2*(n+1))))
      (fun _ τ => Metric.hausdorffDist
        (spectrum ℂ (zigzag H (Equiv.refl _) (fun i => StrongConv.permOp (τ i).val)))
        (spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (H.mat ^ 2)) ∪
          spectrum ℂ (matchingLimit H))) 0 ∧
    ProbConverges (fun n => finiteLaw (Ω := Fin d → Involution (n+2)))
      (fun _ τ => Metric.hausdorffDist
        (spectrum ℂ (zigzag H (Equiv.refl _) (fun i => StrongConv.permOp (τ i).val)))
        (spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (H.mat ^ 2)) ∪
          spectrum ℂ (matchingLimit H))) 0) := by sorry

end ZigZagStrong.ZigZag.Supplement
