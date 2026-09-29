-- Prove2me | solution 1 for PriceOfUniversality.indicator_invariance_price
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:07:22.886956+00:00
-- url     : https://prove2.me/submissions/738fb9c7-5101-40e2-bcee-00a8a20b2929

-- Sol generated from Novelty/UniversalRedundancyInvariance.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyInvariance
import Definitions.Def_Novelty_UniversalRedundancySharpness
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_exists_eq_maxLik
import Theorems.Thm_PriceOfUniversality_indicatorClass_disjoint
import Theorems.Thm_PriceOfUniversality_indicatorClass_isPMF
import Theorems.Thm_PriceOfUniversality_le_maxLik
import Theorems.Thm_PriceOfUniversality_shtarkov_disjointSupports
import Theorems.Thm_PriceOfUniversality_shtarkov_pos
/-
# The price of universality, VIII: an invariance theorem with an explicit price

Algorithmic information theory's invariance theorem says that two universal
machines differ by an additive constant, but the constant is opaque.  In the
statistical setting the constant is *computable*: if `P' ⊆ P` are classes of
sources and `U'`, `U` are their normalised maximum likelihood codes, then on
every message the specialised code `U'` beats the more general code `U` by at
most

  `log₂ S(P) − log₂ S(P')`  bits,

i.e. exactly the ratio of the two Shtarkov normalisers, and this is **attained**
on any message whose maximum likelihood is achieved inside the subclass
(`nml_excess_eq`).  A concrete witness — the `m` deterministic sources with the
one-element subclass — realises the full `log₂ m` bits
(`indicator_invariance_price`), so the bound is not vacuous.

Reading this back into the research programme: **the entire benefit of a
specialised decompressor is the logarithm of how much model class it throws
away.**  Nothing else about the specialisation matters.
-/

open PriceOfUniversality

open Finset Real


variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ Θ' : Type*} [Fintype Θ] [Nonempty Θ] [Fintype Θ'] [Nonempty Θ']


omit [Nonempty A] [Fintype Θ] [Nonempty Θ] [Fintype Θ'] [Nonempty Θ'] in
theorem subClass_isPMF {p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) (e : Θ' → Θ) (t : Θ') :
    IsPMF (subClass p e t) := hp (e t)




omit [Nonempty A] in
/-- **Sharpness of the invariance price.**  On a message whose maximum
likelihood is already attained inside the subclass, the specialised code saves
exactly `log₂ (S(P) / S(P'))` bits — no more and no less. -/
theorem nml_excess_eq {p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) (e : Θ' → Θ) (a : A)
    (hpos : 0 < maxLik (subClass p e) a)
    (heq : maxLik (subClass p e) a = maxLik p a) :
    logb 2 (nml (subClass p e) a) - logb 2 (nml p a)
      = logb 2 (shtarkov p) - logb 2 (shtarkov (subClass p e)) := by
  have hsub : 0 < shtarkov (subClass p e) := shtarkov_pos (subClass_isPMF hp e)
  have hS : 0 < shtarkov p := shtarkov_pos hp
  have hpos2 : 0 < maxLik p a := heq ▸ hpos
  simp only [nml]
  rw [Real.logb_div (ne_of_gt hpos) (ne_of_gt hsub),
    Real.logb_div (ne_of_gt hpos2) (ne_of_gt hS), heq]
  ring


/-! ## A one-source subclass, and the exact value of specialising -/


variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]

omit [Fintype A] [Nonempty A] in
theorem maxLik_unique [Unique Θ] (p : Θ → A → ℝ) (a : A) : maxLik p a = p default a := by
  obtain ⟨θ, hθ⟩ := exists_eq_maxLik p a
  rw [hθ, Subsingleton.elim θ (default : Θ)]

omit [Nonempty A] in
/-- A one-element class pays no price of universality: its Shtarkov sum is `1`. -/
theorem shtarkov_unique [Unique Θ] {p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) :
    shtarkov p = 1 := by
  calc shtarkov p = ∑ a, p default a := Finset.sum_congr rfl fun a _ => maxLik_unique p a
    _ = 1 := (hp default).total


variable {m : ℕ}


theorem shtarkov_indicatorSub [NeZero m] : shtarkov (indicatorSub m) = 1 :=
  shtarkov_unique (fun t => subClass_isPMF (fun θ => indicatorClass_isPMF θ) _ t)

theorem shtarkov_indicatorClass [NeZero m] : shtarkov (indicatorClass m) = m := by
  rw [shtarkov_disjointSupports (fun θ => indicatorClass_isPMF θ) indicatorClass_disjoint,
    Fintype.card_fin]

theorem maxLik_indicatorSub_zero [NeZero m] : maxLik (indicatorSub m) (0 : Fin m) = 1 := by
  rw [indicatorSub, maxLik_unique]
  norm_num [subClass, indicatorClass]

theorem maxLik_indicatorClass_zero [NeZero m] : maxLik (indicatorClass m) (0 : Fin m) = 1 := by
  refine le_antisymm ((Finset.sup'_le_iff univ_nonempty _).2 fun θ _ => ?_) ?_
  · simp only [indicatorClass]; split <;> norm_num
  · have := le_maxLik (indicatorClass m) (0 : Fin m) (0 : Fin m)
    simpa [indicatorClass] using this



open PriceOfUniversality in
theorem solution[NeZero m] :
    logb 2 (nml (indicatorSub m) (0 : Fin m)) - logb 2 (nml (indicatorClass m) (0 : Fin m))
      = logb 2 m := by
  have hbase :
      logb 2 (nml (indicatorSub m) (0 : Fin m)) - logb 2 (nml (indicatorClass m) (0 : Fin m))
        = logb 2 (shtarkov (indicatorClass m)) - logb 2 (shtarkov (indicatorSub m)) := by
    refine nml_excess_eq (fun θ => indicatorClass_isPMF θ) _ (0 : Fin m) ?_ ?_
    · rw [show subClass (indicatorClass m) (fun _ : Fin 1 => (0 : Fin m)) = indicatorSub m from rfl,
        maxLik_indicatorSub_zero]
      norm_num
    · rw [show subClass (indicatorClass m) (fun _ : Fin 1 => (0 : Fin m)) = indicatorSub m from rfl,
        maxLik_indicatorSub_zero, maxLik_indicatorClass_zero]
  rw [hbase, shtarkov_indicatorSub, shtarkov_indicatorClass]
  simp
