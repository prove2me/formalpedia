-- Prove2me | Theorems.Thm_ZKSheafPCP_theorem_5_7
-- name    : ZKSheafPCP.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:12:39.451476+00:00
-- url     : https://prove2.me/theorems/491bbcc1-68f9-49c5-9034-ff49fbfe14dd
-- title:
--   Theorem 5.7 — the recursive tester for $(c,d)$-testable covers
-- statement:
--   Let $F$ be a sheaf of linear codes with a $(c,d)$-testable cover of $F_\sigma$, and let $T$ be the recursive test of Construction 5.6. Then:
--
--   1. if $f\in F(P)$, the test never rejects;
--   2. for any $\epsilon>0$, if $\Pr[T(f)\text{ rejects}]\le\epsilon$, then
--   $$\Delta(f|_\sigma,F_\sigma)\le\epsilon\cdot c^d;$$
--   3. the test reads at most $\max_{\alpha\in S_1}|\alpha|$ points, the size of the largest local code at the bottom.
--
--   This is the soundness engine of the PCPP.
--
--   Differences from the source:
--   - reading: "(max_{α∈S1}(|α|))-local codeword ϵ·c^d-tester", with Definition 3.23 rejecting δ-far words with probability at least 1/2 → completeness, Pr[reject] ≤ ϵ ⇒ Δ ≤ ϵ·c^d, and the query count; reason: the proof proves this form, Theorem 7.4 uses it, and Definition 3.23 cannot be meant for small ϵ
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 5.7, p.23; Construction 5.6, p.23

import Mathlib
import Definitions.Def_ZKSheafPCP_TestTree

namespace ZKSheafPCP

open Classical

/-- Theorem 5.7, p.23 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): for a `(c, d)`-testable cover of `F_σ`, Construction 5.6 is a `(max_{α∈S₁} |α|)`-local codeword tester:
(i) it never rejects a codeword of `F(P)`; (ii) for any `ϵ > 0`, if it rejects `f` with probability at most `ϵ`, then
`Δ(f|_σ, F_σ) ≤ ϵ · c^d`; (iii) every leaf it reaches has at most `queries t` points.

**Formalization Note** "`ϵ · c^d`-tester" is read as printed in the proof ("We show that if `Pr[T(f, σ, S) = no] ≤ ϵ` then
`Δ(f|_{P_σ}, F_σ) ≤ ϵ · c^d`"), and as in Theorem 7.4. It cannot mean Definition 3.23's reject-with-probability-`1/2` for small `ϵ`. -/
theorem theorem_5_7 {F D : Type} [Field F] [Fintype D] (PP : CodedSpace D) (𝓕 : LocalCodes F D) (h𝓕 : 𝓕.IsSheaf PP)
    (c d : ℕ) (t : TestTree D) (ht : IsTree 𝓕 PP c t) (hd : t.HasDepth d) :
    (∀ f ∈ 𝓕.sections PP.P, rejectProb 𝓕 t f = 0) ∧
    (∀ (f : D → F) (ϵ : ℝ), 0 < ϵ → rejectProb 𝓕 t f ≤ ϵ →
      LocalCodes.distTo t.root f (𝓕.code t.root) ≤ ϵ * (c : ℝ) ^ d) ∧
    (∀ ρ ∈ t.leafLaw.support, ρ.card ≤ t.queries) := by sorry

end ZKSheafPCP
