-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_Nonabelian_torsor_iff_abelian
-- name    : Bridges.ResidueLeakage.Nonabelian.torsor_iff_abelian
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:36:20.152401+00:00
-- url     : https://prove2.me/theorems/47be73b1-fbb3-4325-a6dc-5d44c68fd6cc
-- title:
--   The torsor structure is equivalent to commutativity.
-- statement:
--   **The torsor structure is equivalent to commutativity.**  The compensator
--   of a candidate is unique up to conjugacy, for every target and candidate, if
--   and only if the group is abelian.  Together with `nonabelian_no_pruning` this
--   closes conjecture C5': a non-abelian channel loses the rigid torsor structure
--   of the quadratic fingerprint, but gains no pruning power whatsoever.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.Nonabelian.torsor_iff_abelian:
--       (∀ σ p q q' : G, classCompatible σ p q → classCompatible σ p q' → IsConj q q') ↔
--         ∀ a b : G, a * b = b * a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/ResidueChannelNonabelianTorsor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/ResidueChannelNonabelianTorsor.lean#L130

-- Thm stub generated from Speculative/AutoResearch/ResidueChannelNonabelianTorsor.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_ResidueChannelNonabelianTorsor
/-
# The non-abelian residue channel: no pruning, but no torsor either (conjecture C5')

Tenth file of the residue-leakage thread.

`Catalog/Bridges/ResidueLeakageTorsorTriviality.lean` proved that the
factorisation fibre of the quadratic-residue fingerprint is a *trivial torsor*:
the set of consistent pairs `(F_A(p), F_A(q))` is exactly one coset of the
anti-diagonal of `{±1}^K`, so every candidate survives and the compensator of a
candidate is unique.  Conjecture C5' of `FUTURE_DIRECTIONS.md` asked what
happens when the abelian character channel is replaced by the **Artin-symbol
channel** of a non-abelian Galois extension: there the datum attached to a
prime is a conjugacy class `C_p ⊆ G`, the datum attached to `N = p·q` is the
class of `σ_N = σ_p σ_q`, and the fibre is
`{(C_p, C_q) : σ_N ∈ C_p · C_q}`.  C5' predicted that this fibre is a *proper*
subset of `Cl(G) × Cl(G)` for non-abelian `G`, i.e. that some candidate classes
are excluded — the first residue-type channel with nonzero pruning.

This file settles C5' in the purely group-theoretic form in which it was
stated, and the answer splits:

* **The pruning half of C5' is FALSE.** `nonabelian_no_pruning`: in *any* group,
  for any target `σ` and any candidate `p`, the element `q = p⁻¹σ` compensates.
  So the projection of the fibre onto the first coordinate is onto every
  conjugacy class; a non-abelian Artin channel prunes exactly nothing either.
  (`classCompatible_conj_left` / `classCompatible_conj_right` check that the
  relation really only depends on the two conjugacy classes, so this is a
  statement about `Cl(G) × Cl(G)`.)
* **The torsor half of C5' is TRUE, and is an exact characterisation.**
  `torsor_iff_abelian`: the compensator of a candidate is unique up to
  conjugacy for *all* targets and candidates **iff** the group is abelian.
  For a non-abelian group there are explicit targets with two non-conjugate
  compensators (`nonabelian_two_nonconj_compensators`), witnessed concretely in
  `S₃` by `perm3_two_nonconj_compensators`.
* The failure is genuinely a class-level phenomenon: at the level of *elements*
  the fibre is always a torsor, of size exactly `|C_p|`
  (`elementFibre_ncard`), for every group, abelian or not.

Conclusion for the thread: no-pruning is not an artefact of commutativity — it
survives every group-theoretic residue channel — while the rigid torsor
structure found for the quadratic fingerprint is *equivalent* to commutativity.
The `2^K`-torsor picture of `ResidueLeakageTorsorTriviality.lean` is therefore
exactly as general as the abelian hypothesis, and no residue channel of this
shape can prune the divisor search.

All statements are proved; no `sorry`, no `axiom`, no `native_decide`.
-/


open Bridges.ResidueLeakage.Nonabelian

variable {G : Type*} [Group G]

theorem Bridges.ResidueLeakage.Nonabelian.torsor_iff_abelian:
    (∀ σ p q q' : G, classCompatible σ p q → classCompatible σ p q' → IsConj q q') ↔
      ∀ a b : G, a * b = b * a := by sorry
