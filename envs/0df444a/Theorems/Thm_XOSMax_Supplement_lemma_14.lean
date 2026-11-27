-- Prove2me | Theorems.Thm_XOSMax_Supplement_lemma_14
-- name    : XOSMax.Supplement.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:37:16.801784+00:00
-- url     : https://prove2.me/theorems/c1fc6c79-8a6e-55bf-bc56-e517f4f60450
-- title:
--   Lemma 14 — a maximal clique maximizes under condition $(*)$
-- statement:
--   Let a signed width-$k$ representation of $f$ satisfy condition $(*)$, and suppose $f(\{v\})>0$ for every ground element. Then some clique $V_i^*$ is inclusion-wise maximal among the representation's cliques and exactly maximizes $f$.
--
--   This identifies the candidate family needed by Theorem 13.
--
--   Differences from the source:
--   - encoding: an XOS function satisfying $(*)$ → a chosen width-$k$ representation satisfying `Represents` and `ConditionStar`; reason: the cliques and condition depend on the representation, as the source's $f_i$ notation does
--   - encoding: finite ground set $V$ and an exact maximizer → a nonempty finite type and a $1$-maximizer on `univ`; reason: these are the same subsets and the same exact inequality
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 14, p.9

import Mathlib
import Definitions.Def_XOSMax_Represents
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_cliqueWrt
import Definitions.Def_XOSMax_Supplement_ConditionStar

namespace XOSMax.Supplement

open XOSMax

/-- **Lemma 14.** Under condition `(∗)`, an inclusion-wise maximal clique maximizes `f`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Lemma 14, p.9).

**Formalization Note** The §2 standing hypothesis `f({v}) > 0` is explicit. Cliques and `(∗)` are
relative to the chosen representation `w`. Maximality forbids strict containment in any other
clique of that representation, and exact maximization is a `1`-maximizer. -/
theorem lemma_14 {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] {k : ℕ}
    (w : Fin k → E → ℝ) (f : Finset E → ℝ) (hrep : Represents w f)
    (hstar : ConditionStar w f) (hpos : ∀ v : E, 0 < f {v}) :
    ∃ i : Fin k,
      (∀ j : Fin k, ¬ cliqueWrt Finset.univ w f i ⊂ cliqueWrt Finset.univ w f j) ∧
      IsMaximizerApprox Finset.univ 1 f (cliqueWrt Finset.univ w f i) := by sorry

end XOSMax.Supplement
