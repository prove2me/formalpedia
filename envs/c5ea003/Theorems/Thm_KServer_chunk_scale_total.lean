-- Prove2me | Theorems.Thm_KServer_chunk_scale_total
-- name    : KServer.chunk_scale_total
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-10T11:17:47.39497+00:00
-- url     : https://prove2.me/theorems/c90e102a-7c57-4b1b-a3e9-1c89ac218eda
-- title:
--   Mass normalisation: the total of a chunk system may be scaled to any smaller value
-- statement:
--   **Mass normalisation for chunk systems with online escapes.**
--
--   Let $C$ be a chunk system with online escapes on a metric space $X$ between the marked points $s,t$, with size floor $0$, size ceiling $c_B$, escape price $p\ge 0$ and chunks $c_1,\dots,c_m$ with sizes $\mathrm{size}(\omega,i)$, in the sense of `KServer.ChunkSystemB`. Write
--   $$\mathbb E[\Sigma]\ =\ \sum_{\omega}P(\omega)\sum_i \mathrm{size}(\omega,i)$$
--   for its expected total mass.
--
--   **Statement.** For every target value $T'$ with $0\le T'\le\mathbb E[\Sigma]$ there is a chunk system $C'$ with the same size floor $0$, the same size ceiling, the same escape price and the same chunk-count bound, whose expected total mass is *exactly* $T'$:
--   $$\sum_{\omega}P'(\omega)\sum_i \mathrm{size}'(\omega,i)\ =\ T'.$$
--   Moreover $C'$ has the same number of chunks as $C$; it inherits constant initial information and nonemptiness of the chunks from $C$; and every Doob jump bound of the total mass of $C$ is again a Doob jump bound for $C'$.
--
--   **Content.** Every requirement a chunk system places on its sizes is monotone downwards: the size window has floor $0$, the total is a lower bound, and the conditional cost axiom
--   $$\mathrm{size}(\omega_0,i)\cdot P\bigl(\text{atom of }\omega_0\text{ at time } i\bigr)\ \le\ \sum_{\omega\ \text{in that atom}}P(\omega)\,\mathrm{cost}_E^{\,\mathrm{bail}}\bigl(\ldots\bigr)$$
--   bounds the size from above by a nonnegative quantity, so it survives multiplication of all sizes by a factor $\lambda\in[0,1]$. Taking $\lambda=T'/\mathbb E[\Sigma]$ (and $\lambda=0$ in the degenerate case $\mathbb E[\Sigma]=0$, where $T'=0$) gives the assertion; the Doob martingale of the total mass is multiplied by the same $\lambda\le1$, so its jumps do not grow.
--
--   The point of the statement is that the *amount* of mass carried by a chunk system may always be trimmed to an exact target without touching its combinatorial data, so that a construction which produces at least the required mass may be assumed to produce exactly it. This is used, for instance, to normalise the output of one level of the induction of Bubeck--Coester--Rabani's Lemma 12 before it is regrouped into the chunks of the next scale, where the regrouping window is stated in terms of the mean chunk mass.
--
--   The nonnegativity of the escape-augmented evader cost, which the argument needs, is elementary: the partial cost $\mathrm{cost}_E(h\chi)-\mathrm{cost}_E(h)$ of an evader on a chunk is a sum of distances, and the escape price is nonnegative.
-- source:
--   Elementary property of the chunk-system model of S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Definition of chunk systems (Section 3, p. 12) and Lemma 12 (p. 14); stated over the platform structure KServer.ChunkSystemB.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

namespace KServer

/-- **Mass normalisation.** The sizes of a chunk system with size floor zero
may be scaled down: for every target `T'` between `0` and the expected total
mass there is a chunk system on the same chunks whose expected total mass is
exactly `T'`. All the structural data — the chunk count, the filtration, the
chunks themselves, the size ceiling and the escape price — are unchanged, and
a Doob jump bound of the total mass is preserved. -/
theorem chunk_scale_total {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL) (hpe : 0 ≤ pe)
    (T' : ℝ) (hT0 : 0 ≤ T') (hT : T' ≤ ∑ ω, C.P ω * ∑ i, C.size ω i)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) :
    ∃ C' : ChunkSystemB X s t 0 cB T' pe mL,
      C'.m = C.m ∧
      (∑ ω, C'.P ω * ∑ i, C'.size ω i) = T' ∧
      ((∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) →
        ∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      ((∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) →
        ∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.DoobJumpBound jb := by sorry

end KServer
