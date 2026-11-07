-- Prove2me | Theorems.Thm_ZKSheafPCP_lemma_6_9
-- name    : ZKSheafPCP.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:12:48.93728+00:00
-- url     : https://prove2.me/theorems/843fe8c5-2a07-4be2-a2c6-a2099ab89795
-- title:
--   Lemma 6.9 — the local simulator has the conditional law of the encoding
-- statement:
--   Let $\sigma\in P$ and let $S\subseteq P$ be a $q$-extendable cover for $F_{\sigma=c'}$ for every $c'\in F_\sigma$. Let $Q\subseteq S$ with $|Q|<q$, $\rho\in S$, $c\in F_\sigma$ and $f\in F_{\sigma=c}(U_Q)$. With $A=U_Q$,
--   $$\Pr_{\pi\leftarrow\mathrm{Sim}_c(f,Q,\rho)}[\pi=\pi^*]=\Pr_{\tilde f\leftarrow\mathrm{ENC}_\sigma(c)}\bigl[\tilde f|_{P_\rho}=\pi^*\ \big|\ \tilde f|_{P_A}=f|_{P_A}\bigr].$$
--
--   This identity says that lazily sampling local codewords reproduces a uniformly random global encoding.
--
--   Differences from the source:
--   - reading: "Let ρ, f, Q, S be the input to the simulator" → the standing hypotheses of Theorem 6.7 and Construction 6.8: Q ⊆ S, |Q| < q, ρ ∈ S, f ∈ F_{σ=c}(U_Q); reason: the lemma refers to them only through "the input to the simulator"
--   - encoding: a conditional probability → a ratio of counts over F_{σ=c}(P); reason: ENC_σ(c) is uniform on that finite set, and the event is nonempty by extendability
--   - encoding: π* ∈ F^{P_ρ} → every zero-padded or other word π* on D; reason: for a word not supported on ρ both sides are 0
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Lemma 6.9, p.27; Construction 6.8 and Theorem 6.7, p.26

import Mathlib
import Definitions.Def_ZKSheafPCP_simLaw

namespace ZKSheafPCP

open Classical

/-- Lemma 6.9, p.27 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): the output of the local simulator `Sim_c(f, Q, ρ)` of Construction 6.8 has the conditional law of the
randomized encoding, `Pr[π = π∗] = Pr_{f̃←ENC_σ(c)}[f̃|_{P_ρ} = π∗ | f̃|_{P_A} = f|_{P_A}]`, `A = U_Q`.

**Formalization Note** The hypotheses are the standing ones of Theorem 6.7 and Construction 6.8 (p.26): `S` is a `q`-extendable cover
for every `F_{σ=c}`, `Q ⊆ S`, `|Q| < q`, `ρ ∈ S`, and `f ∈ F_{σ=c}(U_Q)`. The conditioning event is nonempty by extendability. -/
theorem lemma_6_9 {F D : Type} [Field F] [Fintype F] [Fintype D] (PP : CodedSpace D) (𝓕 : LocalCodes F D)
    (h𝓕 : 𝓕.IsSheaf PP) (σ : Finset D) (hσ : σ ∈ PP.P) (q : ℕ) (S : Finset (Finset D))
    (hS : ∀ c ∈ 𝓕.code σ, 𝓕.IsRelKExtendableCover PP q (PP.geq σ) c S)
    (c : D → F) (hc : c ∈ 𝓕.code σ) (Q : Finset (Finset D)) (hQ : Q ⊆ S) (hQq : Q.card < q)
    (ρ : Finset D) (hρ : ρ ∈ S) (f : D → F) (hf : f ∈ 𝓕.relSections (PP.geq σ) c (PP.closure Q))
    (πs : D → F) :
    ((simLaw 𝓕 PP σ c f Q ρ) πs).toReal = encCond 𝓕 PP σ c f Q ρ πs := by sorry

end ZKSheafPCP
