-- Prove2me | solution 1 for Bridges.ResidueLeakage.Nonabelian.torsor_iff_abelian
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:57:53.205772+00:00
-- url     : https://prove2.me/submissions/dfbae312-1c84-4085-a34e-31661c3e3a51

-- Sol generated from Speculative/AutoResearch/ResidueChannelNonabelianTorsor.lean
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








/-- In a non-abelian group there are a target and a candidate with two
**non-conjugate** compensators: the class-level fibre is not a torsor.
Concretely, for non-commuting `a, b` the target `σ = a` and candidate `p = a`
admit both `q = 1` and `q = (b a b⁻¹)⁻¹ a ≠ 1`. -/
theorem nonabelian_two_nonconj_compensators {a b : G} (hab : a * b ≠ b * a) :
    classCompatible a a 1 ∧ classCompatible a a ((b * a * b⁻¹)⁻¹ * a) ∧
      ¬ IsConj (1 : G) ((b * a * b⁻¹)⁻¹ * a) := by
  refine ⟨⟨a, 1, IsConj.refl _, IsConj.refl _, by group⟩,
    ⟨b * a * b⁻¹, (b * a * b⁻¹)⁻¹ * a,
      ⟨⟨b, b⁻¹, by group, by group⟩, by simp [SemiconjBy]⟩, IsConj.refl _, by group⟩, ?_⟩
  intro hc
  rw [isConj_one_right] at hc
  have hba : b * a * b⁻¹ = a := inv_mul_eq_one.mp hc
  exact hab (by
    calc a * b = b * a * b⁻¹ * b := by rw [hba]
      _ = b * a := by group)











open Bridges.ResidueLeakage.Nonabelian in
theorem solution:
    (∀ σ p q q' : G, classCompatible σ p q → classCompatible σ p q' → IsConj q q') ↔
      ∀ a b : G, a * b = b * a := by
  constructor
  · intro h a b
    by_contra hab
    obtain ⟨h1, h2, h3⟩ := nonabelian_two_nonconj_compensators hab
    exact h3 (h a a 1 _ h1 h2)
  · intro hcomm σ p q q' h1 h2
    obtain ⟨x, y, hx, hy, hxy⟩ := h1
    obtain ⟨x', y', hx', hy', hxy'⟩ := h2
    have key : ∀ {u v : G}, IsConj u v → u = v := by
      intro u v huv
      obtain ⟨c, hc⟩ := huv
      rw [SemiconjBy] at hc
      exact mul_left_cancel (a := (c : G)) (by rw [hc, hcomm])
    have hq : q = y := key hy
    have hq' : q' = y' := key hy'
    have hxx : x = x' := (key hx).symm.trans (key hx')
    have hyy : y = y' := mul_left_cancel (a := x) (by rw [hxy, hxx, hxy'])
    rw [hq, hq', hyy]
