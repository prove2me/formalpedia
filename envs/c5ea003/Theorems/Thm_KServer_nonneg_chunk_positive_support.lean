-- Prove2me | Theorems.Thm_KServer_nonneg_chunk_positive_support
-- name    : KServer.nonneg_chunk_positive_support
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T17:22:41.779173+00:00
-- url     : https://prove2.me/theorems/072b394e-4102-4ab2-a77f-61d242e156fd
-- title:
--   Positive-support conversion preserves chunk certificates and Doob jumps
-- statement:
--   Let $D$ be a finite chunk certificate on a metric space, with marked points $s,t$, size window $[c_{\mathrm{Lo}},c_{\mathrm{Hi}}]$, expected-total requirement $T$, escape price $p$, and minimum chunk count $m_0$. Its weights are nonnegative and sum to one. Assume constant initial information, nonempty chunks, and a Doob-jump bound $j$ on positive-weight outcomes.
--
--   There is a strict positive-weight chunk system $C$ with exactly the same parameters and chunk count, together with an injection $e:\Omega_C\hookrightarrow\Omega_D$, such that
--
--   $$P_C(\omega)=P_D(e\omega),\qquad \sum_{\omega\in\Omega_C}P_C(\omega)f(e\omega)=\sum_{\omega\in\Omega_D}P_D(\omega)f(\omega)$$
--
--   for every real function $f$ on the original outcome space. The histories agree under the injection, and the actual expected total sizes agree:
--
--   $$\mathbb E_C\!\left[\sum_i c_i\right]=\mathbb E_D\!\left[\sum_i c_i\right].$$
--
--   The resulting system has constant initial information, nonempty chunks, and the same Doob-jump bound. As a strict chunk system it satisfies all the original conditional online-cost inequalities, terminal-request and offline-cost conditions, and size-window and expected-total requirements.
--
--   This permits finite constructions to use zero-weight outcomes, including impossible branches in stopped processes, while producing a certificate in the platform's original positive-weight model. No probabilities are renormalized.
--
--   **Formalization Note** The proof constructs the positive support as a subtype and uses total real division. Weighted sums over every history atom are preserved, so the conditional expected totals and their jumps agree on the retained outcomes.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a and stopping rule (1), and Section 4.2, equations (3)–(4), printed pp. 16–19. Elementary finite-support restriction theorem for the platform definitions KServer_nonneg_chunk_system and KServer_chunk_system_b; this bookkeeping lemma is proved here, not quoted as a separate result of the paper.

import Definitions.Def_KServer_nonneg_chunk_system

set_option autoImplicit false
open KServer
open scoped BigOperators

theorem KServer.nonneg_chunk_positive_support {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price jb : ℝ} {mLo : ℕ}
    (D : NonnegChunkSystemB X s t cLo cHi total price mLo)
    (h0 : ∀ ω ω' : D.Ω, D.hist 0 ω = D.hist 0 ω')
    (hch : ∀ (ω : D.Ω) (i : Fin D.m), D.chunk ω i ≠ [])
    (hjump : D.DoobJumpBound jb) :
    ∃ (C : ChunkSystemB X s t cLo cHi total price mLo) (e : C.Ω ↪ D.Ω),
      C.m = D.m ∧
      (∀ ω, C.P ω = D.P (e ω)) ∧
      (∀ f : D.Ω → ℝ, (∑ ω, C.P ω * f (e ω)) = ∑ ω, D.P ω * f ω) ∧
      (∀ h ω, C.hist h ω = D.hist h (e ω)) ∧
      (∑ ω, C.P ω * ∑ i, C.size ω i) = (∑ ω, D.P ω * ∑ i, D.size ω i) ∧
      (∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω') ∧
      (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
      C.DoobJumpBound jb := by sorry
