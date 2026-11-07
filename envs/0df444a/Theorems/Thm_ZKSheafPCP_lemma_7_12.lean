-- Prove2me | Theorems.Thm_ZKSheafPCP_lemma_7_12
-- name    : ZKSheafPCP.lemma_7_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:13:25.2082+00:00
-- url     : https://prove2.me/theorems/9340545b-c061-4316-ae57-fb2659c3441e
-- title:
--   Lemma 7.12 — gluing preserves $d$-testability
-- statement:
--   Let $F$ be the output of Construction 7.5 on $F[t]$, $\sigma$, a $c$-testable cover $S$ for $F[t]_\sigma$, and sheaves $F[\rho]$ that are $(c,d-1)$-testable for $F[\rho]_{\sigma_\rho}$. Then $F$ is a $(c,d)$-testable sheaf code for $F_{h_t(\sigma)}$.
--
--   This is the inductive step behind the short PCPP: testing $F_\sigma$ is reduced to testing smaller codes through glued sheaves.
--
--   Differences from the source:
--   - reading: "d-testable", with d−1 implicit in the input of Construction 7.5 → the same constant c throughout, and d of the page written as d+1; reason: Definition 5.2 uses one c along a tree, which the recursion needs
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Lemma 7.12, p.34; Construction 7.5, p.32

import Mathlib
import Definitions.Def_ZKSheafPCP_GluingInput

namespace ZKSheafPCP

open Classical

/-- Lemma 7.12, p.34 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): the output `F` of Construction 7.5 is a `d`-testable sheaf code for `F_{h_t(σ)}`, when `S` is a testable
cover for `F[t]_σ` and each `F[ρ]` is a `(d - 1)`-testable sheaf code for `F[ρ]_{σ_ρ}`, all with the same constant `c`.

**Formalization Note** `d` of the page is `d + 1` here. -/
theorem lemma_7_12 {F Dt : Type} [Field F] [Fintype Dt] (I : GluingInput F Dt) (Pout : CodedSpace I.GluedDom)
    (G : LocalCodes F I.GluedDom) (hG : I.IsGluedOutput Pout G) (c d : ℕ) (μ : PMF (Finset Dt))
    (hS : IsTestableCover I.Ft I.Pt c I.σ I.S μ)
    (hr : ∀ ρ ∈ I.S, IsTestableSheaf (I.Fr ρ) (I.Pr ρ) c d (I.σr ρ)) :
    IsTestableSheaf G Pout c (d + 1) (I.σ.image Sum.inl) := by sorry

end ZKSheafPCP
