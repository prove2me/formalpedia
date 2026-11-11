-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_spectral_convergence
-- name    : ZigZagStrong.ZigZag.spectral_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:21.545084+00:00
-- url     : https://prove2.me/theorems/307ebc80-0659-4b0c-b438-7e9e179261d5
-- title:
--   Theorem 3.8 — strong convergence gives the entire new spectrum
-- statement:
--   Fix a finitely generated group $\Gamma$, a finite symmetric generating set $S$, and any $c$-regular gadget $H$ on $S$. Let $\pi_n$ be measurable random actions on finite sets, whose restrictions to $1^\perp$ converge strongly in probability to the left regular representation $\lambda$. Then
--   $$d_H(\operatorname{spec}_{\rm new}(G_{\pi_n}\mathbin{z}H),\operatorname{spec}(G_\lambda\mathbin{z}H))\longrightarrow0.$$
--   Both the upper and lower edges of the new spectra converge in probability to their respective limiting edges. No vertex transitivity or goodness is imposed here. This transfers the group-representation input to the full zig-zag spectrum.
--
--   Differences from the source:
--   - encoding: Finite vertex sets and real self-adjoint spectra → Fin-indexed vertex sets and complex operator spectra with their full Hausdorff distance; reason: Finite sets are transported along bijections; real-axis inclusion preserves distances and spectra.
--   - encoding: Finite random actions and their new spectra → Explicit measurability of generator events; reason: Measurability is the standing meaning of a random action. Strong convergence itself forces the constants-perpendicular spaces to be eventually nonzero; no additional size hypothesis is imposed. The empty-port product has empty spectra on both sides and its distance is totalized as zero.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Theorem 3.8, p. 12.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem spectral_convergence {Γ : Type*} [Group Γ] {d c : ℕ} (S : Generators Γ d)
  (H : Gadget d c) (k : ℕ → ℕ)
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
  [∀ n, IsProbabilityMeasure (μ n)]
  (π : ∀ n, Ω n → Γ →* Equiv.Perm (Fin (k n)))
  (hm : ∀ n i (A : Set (Equiv.Perm (Fin (k n)))),
    MeasurableSet {ω | π n ω (S.gen i) ∈ A})
  (hs : StrongConvergence (fun n A => (μ n).real A)
    (fun n ω i => StrongConv.permOpPerp (π n ω (S.gen i)))
    (fun i => regularL2 (S.gen i))) :
  ProbConverges (fun n A => (μ n).real A)
    (fun n ω => spectrumDistance (newAdj H S.flip (fun i => π n ω (S.gen i)))
      (zigzag H S.flip (fun i => regularL2 (S.gen i)))) 0 ∧
  ProbConverges (fun n A => (μ n).real A)
    (fun n ω => topEdge (newAdj H S.flip (fun i => π n ω (S.gen i))))
    (topEdge (zigzag H S.flip (fun i => regularL2 (S.gen i)))) ∧
  ProbConverges (fun n A => (μ n).real A)
    (fun n ω => bottomEdge (newAdj H S.flip (fun i => π n ω (S.gen i))))
    (bottomEdge (zigzag H S.flip (fun i => regularL2 (S.gen i)))) := by sorry

end ZigZagStrong.ZigZag
