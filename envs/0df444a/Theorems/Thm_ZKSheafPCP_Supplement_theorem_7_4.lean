-- Prove2me | Theorems.Thm_ZKSheafPCP_Supplement_theorem_7_4
-- name    : ZKSheafPCP.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T07:25:12.350234+00:00
-- url     : https://prove2.me/theorems/c84f93b9-6624-44d0-b047-11782f961018
-- title:
--   Theorem 7.4 (corrected: proximity endpoints and range) — perfect zero-knowledge PCPP from a testable, extendable sheaf code
-- statement:
--   Let $\mathbb F$ be a finite field and let $\mathcal F$ be a $(c,d)$-testable sheaf code for the local code $\mathcal F_\sigma$, with recursive test tree and top test cover $S$. Suppose there is one $\kappa\in\mathbb N$ and one simulation cover such that, for every honest input $w\in\mathcal F_\sigma$, that cover is $\kappa$-extendable for $\mathcal F_{\sigma=w}$. The simulation cover need not equal the test tree's top cover.
--
--   For every $\epsilon\in[0,1]$ such that $\epsilon=0$ or $c^d>0$, and such that $c^d\epsilon\le1$, there are actual bounds $l_S,t_S$ supplied by corrected Theorem 6.7 for which Construction 7.3 is a black-box $l_S(\kappa)$-local perfect zero-knowledge PCPP for $\mathcal F_\sigma$ with
--
--   $$
--   \text{query complexity }\max_{\alpha\in S_1}|\alpha|,\qquad
--   \text{query bound }\kappa,\qquad
--   \text{soundness error }1-\epsilon,\qquad
--   \text{proximity }c^d\epsilon.
--   $$
--
--   The prover is fixed to the uniform global-extension prover of Construction 7.3. The virtual word uses the implicit input on $P_\sigma$ and the proof only off $P_\sigma$.
--
--   Differences from the source:
--   - correction: every $\epsilon\in[0,1]$ → every $\epsilon\in[0,1]$ with $\epsilon=0$ or $c^d>0$; reason: when $c=0$, $d>0$ and $\epsilon>0$, the printed proximity is zero, so every codeword is zero-far under Definition 3.25 and perfect completeness contradicts soundness error $1-\epsilon$
--   - correction: proximity parameter $c^d\epsilon$ for every $\epsilon\in[0,1]$ → additionally $c^d\epsilon\le1$; reason: Definition 3.25 requires a proximity parameter in $[0,1]$, while the printed hypotheses permit $c^d\epsilon>1$
--   - reading: “there exists $\kappa$ such that $\mathcal F_{\sigma=c}$ has a $\kappa$-extendable cover,” with $c$ and the cover free → one $\kappa$ and one simulation cover work for every $w\in\mathcal F_\sigma$, without identifying that cover with the test tree's top cover; reason: a single PCPP simulator is fixed before the honest input, while the page does not say the simulation and test covers coincide
--   - encoding: $l_S$ is “a function defined in Theorem 6.7” → existential actual query/clock bounds satisfying corrected Theorem 6.7, together with the resulting operational local simulator; reason: this makes the dependency on Theorem 6.7 explicit and excludes the vacuous zero bounds admitted by the printed quantifiers
--   - encoding: Construction 7.3 as prose → a `PCPPFamily` whose sole explicit instance encodes $(P,\mathcal F,\sigma,S)$ and its test tree, with the uniform-extension prover exposed by `IsPZKPCPPWithProver` and the same parameters also asserted through `IsPZKPCPP`; reason: this fixes the constructed prover and gives the verifier and simulator meaningful clocks
--   - encoding: $\max_{\alpha\in S_1}|\alpha|$ → `TestTree.queries`; reason: the published test-tree definition computes exactly the maximum size of a leaf reached by the recursive tester
--   - encoding: uniform prover distribution on $\mathcal F_{\sigma=w}(P)$ → `uniformOn` with the zero word as a default only if that set is empty; reason: the uniform extendability hypothesis makes the set nonempty for every honest input, so the default changes no theorem instance
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 7.4, p.32

import Mathlib
import Definitions.Def_ZKSheafPCP_Supplement_Construction73Data
import Definitions.Def_ZKSheafPCP_Supplement_IsLocallySimulatable
import Definitions.Def_ZKSheafPCP_simLaw
import Definitions.Def_ZKSheafPCP_TestTree

namespace ZKSheafPCP.Supplement

open Classical

/-- Theorem 7.4, p.32 (Zeilberger, O'Connor, Gur, Spooner,
*Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*,
STOC 2027 submission, manuscript sha256 ac5e528f…): Construction 7.3 for a
`(c,d)`-testable sheaf code, using one simulation cover that is `κ`-extendable
for every honest input word, is a black-box `lS(κ)`-local perfect zero-knowledge PCPP.
Its verifier makes `max_{α∈S₁}|α|` queries, represented by `test.queries`; its
zero-knowledge query bound is `κ`, soundness error is `1-ϵ`, and proximity is
`c^d·ϵ`.

The first conjunct fixes the prover to the uniform-extension prover printed in
Construction 7.3. The second exposes the same parameters through the published
`IsPZKPCPP` interface. In `construction73VirtualWord`, the implicit input supplies
all coordinates in `P_σ`, so a conflicting purported proof cannot overwrite it.

**Formalization Note** The page leaves the codeword `c` free in “`F_{σ=c}` has a
`κ`-extendable cover”; this is read uniformly, with one simulation cover and `κ`
before every `w ∈ F_σ`, as required for one PCPP. The simulation cover need not
be the test tree's top cover; the page does not identify them. The additional condition
`ϵ = 0 ∨ 0 < c^d` corrects the degenerate printed endpoint: if `c = 0`, `d > 0`
and `ϵ > 0`, the proximity parameter is zero, so under Definition 3.25 every
codeword is zero-far; perfect completeness then contradicts soundness error
`1-ϵ`. The bound `c^d·ϵ ≤ 1` keeps the proximity parameter in Definition 3.25's
declared interval. No endpoint is removed in the parameter regime used by the paper. -/
theorem theorem_7_4 {F D : Type} [Field F] [Fintype F] [Fintype D]
    (I : Construction73Data F D) (h𝓕 : I.sheaf.IsSheaf I.PP)
    (hσ : I.sigma ∈ I.PP.P) (c d κ : ℕ)
    (htree : IsTree I.sheaf I.PP c I.test)
    (hdepth : I.test.HasDepth d) (hroot : I.test.root = I.sigma)
    (htop : ∃ μ child, I.test = .node I.sigma I.cover μ child)
    (simCover : Finset (Finset D))
    (hcover : ∀ w ∈ I.sheaf.code I.sigma,
      I.sheaf.IsRelKExtendableCover I.PP κ (I.PP.geq I.sigma) w simCover)
    (ϵ : ℝ) (hϵ0 : 0 ≤ ϵ) (hϵ1 : ϵ ≤ 1)
    (hdeg : ϵ = 0 ∨ 0 < (c : ℝ) ^ d)
    (hprox : (c : ℝ) ^ d * ϵ ≤ 1) :
    ∃ lS tS : ℕ → ℕ,
      (∀ k, lS k ≤ (k + 1) * simCover.sup (fun τ => (τ ∩ I.sigma).card)) ∧
      PolyBddIn tS (fun k => (k + 1) * simCover.sup Finset.card) ∧
      IsLocallySimulatable (fun w : I.sheaf.code I.sigma => (w : D → F))
        (extensionEncoding I.PP I.sheaf I.sigma) simCover tS lS κ ∧
      IsPZKPCPPWithProver (D := D) (construction73Family I) (construction73Prover I)
          (fun _ => I.test.queries) (fun _ => 1 - ϵ) (fun _ => (c : ℝ) ^ d * ϵ)
          (fun _ => κ) (fun _ => lS κ) ∧
        IsPZKPCPP (construction73Family I) (fun _ => Fintype.card D)
          (fun _ => I.test.queries) (fun _ => 1 - ϵ) (fun _ => (c : ℝ) ^ d * ϵ)
          (fun _ => κ) (fun _ => lS κ) := by sorry

end ZKSheafPCP.Supplement
