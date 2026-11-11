-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_trivial_spectrum
-- name    : ZigZagStrong.ZigZag.trivial_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:52.588204+00:00
-- url     : https://prove2.me/theorems/52c1cf8b-74cb-48ff-826f-4e05afd199a8
-- title:
--   Proposition 3.11 — natural identification of the whole trivial operator
-- statement:
--   Let $\Gamma$ act on a finite nonempty vertex set $V$, let $S$ be its specified symmetric generators, and let $H$ be a $c$-regular gadget on $S$. Let $F_Se_s=e_{s^{-1}}$. Under the natural isometric identification of cloud-constant vectors with $\ell^2(S)$,
--   $$Z_\pi|_{\mathcal H_{\rm triv}}=A_HF_SA_H,\qquad \operatorname{spec}_{\rm triv}(G_\pi z H)=\operatorname{spec}(A_HF_SA_H).$$
--   The operator identification and its spectral consequence are both included. All $d$ trivial eigenvalues are retained.
--
--   Differences from the source:
--   - encoding: Natural identification on a finite vertex set → Compression through normalized constants, with n>0; reason: Normalization is isometric; nonemptiness is the standing convention needed for the source d-dimensional trivial space.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Proposition 3.11, p. 14.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem trivial_spectrum {Γ : Type*} [Group Γ] {d c n : ℕ} (S : Generators Γ d)
  (H : Gadget d c) (hn : 0 < n) (π : Γ →* Equiv.Perm (Fin n)) :
  trivialAdj H S.flip (fun i => π (S.gen i)) =
    Matrix.toEuclideanCLM (𝕜 := ℂ) (H.mat * (∑ i, elementary i (S.flip i)) * H.mat) ∧
  spectrum ℂ (trivialAdj H S.flip (fun i => π (S.gen i))) =
    spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (H.mat * (∑ i, elementary i (S.flip i)) * H.mat)) := by sorry

end ZigZagStrong.ZigZag
