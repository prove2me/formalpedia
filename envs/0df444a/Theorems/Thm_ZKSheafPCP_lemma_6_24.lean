-- Prove2me | Theorems.Thm_ZKSheafPCP_lemma_6_24
-- name    : ZKSheafPCP.lemma_6_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:11:37.191458+00:00
-- url     : https://prove2.me/theorems/240bce50-f2ea-48f0-ade2-9f73e5af6fbe
-- title:
--   Lemma 6.24 — MDS local codes give extendability from a domain count
-- statement:
--   Let $F$ be a sheaf code over a finite field on a coded space $P$, and let $\sigma\in P$ with $F_\sigma$ maximum distance separable. Let $U\subseteq P$ be an upper set. If
--   $$|P_\sigma\cap P_U|\le\dim(F_\sigma),$$
--   then $U$ is extendable to $U\cup P_{\ge\sigma}$, and if $|P_\sigma\cap P_U|=\dim(F_\sigma)$, then $U$ is uniquely extendable to $U\cup P_{\ge\sigma}$.
--
--   This turns extendability into counting, and is how the rows and columns of the Reed-Muller sheaf are handled in Theorem 8.3.
--
--   Differences from the source:
--   - encoding: Δ_C = |D| − dim(C) + 1 (Definition 3.17) → every nonzero word has weight at least |σ| − dim C + 1; the zero code counts as MDS; reason: the Singleton bound gives the other direction for a nonzero code, and the zero code has no minimum distance
--   - reading: F (the field of the paper) → a finite field; reason: the paper works over finite fields throughout §3.1 and §4
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Lemma 6.24, p.30

import Mathlib
import Definitions.Def_ZKSheafPCP_LocalCodes

namespace ZKSheafPCP

open Classical

/-- Lemma 6.24, p.30 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): if the local code `F_σ` is MDS and `U` is an upper set, then `|P_σ ∩ P_U| ≤ dim F_σ` makes `U`
extendable to `U ∪ P⩾σ`, and `|P_σ ∩ P_U| = dim F_σ` makes it uniquely extendable.

**Formalization Note** The field is finite and the sheaf general. `P_σ = σ` in set-family form. -/
theorem lemma_6_24 {F D : Type} [Field F] [Fintype F] [Fintype D] (PP : CodedSpace D) (𝓕 : LocalCodes F D)
    (h𝓕 : 𝓕.IsSheaf PP) (σ : Finset D) (hσ : σ ∈ PP.P) (hMDS : IsMDS σ (𝓕.code σ))
    (U : Finset (Finset D)) (hU : PP.IsUpper U) :
    ((σ ∩ supp U).card ≤ Module.finrank F (𝓕.code σ) → 𝓕.Extendable U (U ∪ PP.geq σ)) ∧
    ((σ ∩ supp U).card = Module.finrank F (𝓕.code σ) → 𝓕.UniquelyExtendable U (U ∪ PP.geq σ)) := by sorry

end ZKSheafPCP
