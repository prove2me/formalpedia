-- Prove2me | Theorems.Thm_burau_faithful_three_of_word_criterion
-- name    : burau_faithful_three_of_word_criterion
-- status  : Open
-- author  : @lt9
-- created : 2026-09-30T19:17:34.563381+00:00
-- url     : https://prove2.me/theorems/2bf2eda1-9f54-441b-8a90-b54271cd0f02
-- title:
--   The Burau word criterion implies faithfulness for B_3
-- statement:
--   **From the word criterion to faithfulness of the Burau representation of $B_3$.**
--
--   Let $\rho_3 : B_3 \to \mathrm{GL}_3(\mathbb{Z}[t,t^{-1}])$ be the unreduced Burau representation and
--   assume the *word criterion*: for every word $w$ in the free group on the two Artin generators,
--   $$\rho_3\bigl([w]\bigr)=1 \iff w\in\bigl\langle\!\bigl\langle\,\sigma_1\sigma_2\sigma_1(\sigma_2\sigma_1\sigma_2)^{-1}\,\bigr\rangle\!\bigr\rangle .$$
--   Since Artin's relations on three strands generate the same normal closure as the single braid relation
--   (proved here as `normalClosure_braidRels_three`), the criterion says exactly that the class of a word is
--   trivial in $B_3$ if and only if its image under $\rho_3$ is trivial. Hence
--   $$\operatorname{Injective}(\rho_3).$$
--   This isolates the combinatorial input (the criterion) from the group-theoretic assembly, and together
--   with the separately proved easy direction of the criterion decomposes the milestone target
--   `BurauFaithful.burau_faithful_three` into two provable children.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3 (Theorem 3.15); W. Magnus, A. Peluso, *On a theorem of V. I. Arnold*, Comm. Pure Appl. Math. 22 (1969).

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

namespace BurauFaithful

open BraidsLinksMCG

/-- The single braid relation for three strands, as a word in the free group on two generators. -/
def braidRel3 : FreeGroup (Fin 2) :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
    (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹

lemma braidRels_three_eq_singleton :
    braidRels 3 = {r | ∃ i j : Fin 2, (j : ℕ) = (i : ℕ) + 1 ∧
      r = FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
            (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹} := by
  ext r
  simp only [braidRels, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨i, j, h, rfl⟩ | h)
    · exfalso
      have hi : (i : ℕ) < 2 := i.isLt
      have hj : (j : ℕ) < 2 := j.isLt
      omega
    · exact h
  · exact Or.inr

lemma braidRels_three_subset :
    braidRels 3 ⊆ ({braidRel3} : Set (FreeGroup (Fin 2))) := by
  intro r hr
  rw [braidRels_three_eq_singleton] at hr
  obtain ⟨i, j, hij, rfl⟩ := hr
  have hi : (i : ℕ) < 2 := i.isLt
  have hj : (j : ℕ) < 2 := j.isLt
  have hi0 : (i : ℕ) = 0 := by omega
  have hj1 : (j : ℕ) = 1 := by omega
  have hieq : i = (0 : Fin 2) := Fin.ext hi0
  have hjeq : j = (1 : Fin 2) := Fin.ext hj1
  subst hieq; subst hjeq
  simp [braidRel3]

lemma singleton_subset_braidRels_three :
    ({braidRel3} : Set (FreeGroup (Fin 2))) ⊆ braidRels 3 := by
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  subst hr
  rw [braidRels_three_eq_singleton]
  exact ⟨0, 1, rfl, rfl⟩

/-- The normal closure of Artin's relations on three strands is the normal closure of the single braid
relation: `B₃ = ⟨σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂⟩`. -/
lemma normalClosure_braidRels_three :
    Subgroup.normalClosure (braidRels 3) =
      Subgroup.normalClosure ({braidRel3} : Set (FreeGroup (Fin 2))) :=
  le_antisymm
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (braidRels_three_subset hx))
    (Subgroup.normalClosure_le_normal fun _ hx =>
      Subgroup.subset_normalClosure (singleton_subset_braidRels_three hx))

end BurauFaithful

theorem burau_faithful_three_of_word_criterion
    (hc : ∀ w : FreeGroup (Fin 2),
      BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 ↔
        w ∈ Subgroup.normalClosure ({BurauFaithful.braidRel3} : Set (FreeGroup (Fin 2)))) :
    Function.Injective (BurauFaithful.burauRep 3) := by sorry
