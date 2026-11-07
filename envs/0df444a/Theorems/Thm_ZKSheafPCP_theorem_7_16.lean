-- Prove2me | Theorems.Thm_ZKSheafPCP_theorem_7_16
-- name    : ZKSheafPCP.theorem_7_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:13:35.230203+00:00
-- url     : https://prove2.me/theorems/3a5e8d2f-f671-4f96-ae3b-fe7cc881f745
-- title:
--   Theorem 7.16 — gluing preserves extendable covers
-- statement:
--   Suppose that for all $c\in F[t]_\sigma$, $S$ is a $\kappa$-extendable cover for $F[t]_{\sigma=c}$, and that for all $\rho\in S$, $P[\rho]_{\ge\sigma_\rho}$ is globally extendable with respect to $F[\rho]$. Then for the output $F$ of Construction 7.5 and all $c\in F[t]_\sigma$, the images of the whole pieces $\{h_\rho(P[\rho]_*):\rho\in S\}$ form a $\kappa$-extendable cover for $F_{h_t(\sigma)=h_t(c)}$.
--
--   Together with Lemma 7.12 this carries the extendability of Theorem 8.3 through the recursion.
--
--   Differences from the source:
--   - reading: g_ρ, C and P[ρ]⩾h_{t,ρ}, which are not defined on the page → h_ρ, F[t]_σ and P[ρ]⩾σ_ρ; reason: the proof uses h_ρ, c ∈ F[t]_σ and the image of h_{t,ρ} (Construction 7.5)
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 7.16, p.35; Construction 7.5, p.32

import Mathlib
import Definitions.Def_ZKSheafPCP_GluingInput

namespace ZKSheafPCP

open Classical

/-- Theorem 7.16, p.35 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): if for all `c ∈ F[t]_σ`, `S` is a `κ`-extendable cover for `F[t]_{σ=c}`, and for all `ρ ∈ S`, `P[ρ]⩾σ_ρ` is globally
extendable with respect to `F[ρ]`, then for all `c ∈ F[t]_σ`, `{h_ρ(P[ρ]∗) : ρ ∈ S}` is a `κ`-extendable cover for `F_{h_t(σ)=h_t(c)}`.

**Formalization Note** The page's `g_ρ` is `h_ρ` and its `C` is `F[t]_σ`. `P[ρ]⩾h_{t,ρ}` is `P[ρ]⩾σ_ρ`, the image of `h_{t,ρ}`. -/
theorem theorem_7_16 {F Dt : Type} [Field F] [Fintype Dt] (I : GluingInput F Dt) (Pout : CodedSpace I.GluedDom)
    (G : LocalCodes F I.GluedDom) (hG : I.IsGluedOutput Pout G) (κ : ℕ)
    (hext : ∀ c ∈ I.Ft.code I.σ, I.Ft.IsRelKExtendableCover I.Pt κ (I.Pt.geq I.σ) c I.S)
    (hgl : ∀ ρ ∈ I.S, (I.Fr ρ).GloballyExtendable (I.Pr ρ) ((I.Pr ρ).geq (I.σr ρ)))
    (c : Dt → F) (hc : c ∈ I.Ft.code I.σ) :
    G.IsRelKExtendableCover Pout κ (Pout.geq (I.σ.image Sum.inl)) (I.pushT c)
      (I.S.attach.image fun ρ => Finset.univ.image (I.embed ρ.1 ρ.2)) := by sorry

end ZKSheafPCP
