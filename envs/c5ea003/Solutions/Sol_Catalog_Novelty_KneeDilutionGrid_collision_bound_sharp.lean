-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.collision_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:16:46.34177+00:00
-- url     : https://prove2.me/submissions/38909018-1b29-49a1-8088-9fac04846267

-- Sol generated from Novelty/KneeCollisionBound.lean
import Mathlib
import Definitions.Def_Novelty_KneeCollisionBound
import Definitions.Def_Novelty_KneeDilutionGrid
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_knee_scaled
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_const_mul
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_unif

/-!
# An information-theoretic lower bound for the memory knee (NET-72, round 3)

`Novelty.KneeDilutionGrid` derived the knee of a diluted profile from the
tokens-per-word ratio.  That is a *mechanistic* explanation and it needs the
tokenizer.  This file gives a **tokenizer-free** lower bound for the knee in
terms of a single scalar statistic of the attention profile, its **collision
mass** (Rényi-2 mass) `collisionMass p k = ∑_{i<k} p i ^ 2`:

* `prefixMass_sq_le_collision` — Cauchy–Schwarz: `(∑_{i<k} p i)² ≤ k · ∑_{i<k} p i²`.
* `knee_ge_of_collision` — hence if the collision mass never exceeds `C`, then
  `knee p tau ≥ tau² / C`.  Flat (high-entropy, low-collision) attention forces a
  large knee; peaked attention permits a small one.
* `collisionMass_tokenSplit` — dilution by `r` divides the collision mass by `r`
  exactly, so the entropy bound is amplified by `r`
  (`dilution_amplifies_collision_bound`): the information-theoretic route
  reproduces the multiplicative law of `dilution_law` *without* referring to the
  tokenizer.  Two independent derivations of the same scaling.
* `collision_bound_sharp` — the bound is attained by the flat profile, so no
  better function of the collision mass exists.

Read against NET-72: the French cell is predicted to have a smaller collision
mass (flatter attention) than the English cell at the same context length, and
`knee ≥ tau²/C` then puts the knee beyond the arithmetic grid.  The bound is
measurable from attention maps alone, which makes it a falsifiable successor to
the tokens-per-word hypothesis.
-/

open Catalog.Novelty.KneeDilutionGrid

open Finset








/-! ### Sharpness -/

lemma collisionMass_scaled (c : ℝ) (n k : ℕ) :
    collisionMass (scaled c n) k = c ^ 2 * (min k n : ℕ) := by
  have h : ∀ i ∈ range k, (scaled c n i) ^ 2 = c ^ 2 * unif n i := by
    intro i _
    unfold scaled unif
    split_ifs <;> ring
  unfold collisionMass
  rw [Finset.sum_congr rfl h]
  have h2 : ∑ i ∈ range k, c ^ 2 * unif n i = prefixMass (fun i => c ^ 2 * unif n i) k := rfl
  rw [h2, prefixMass_const_mul, prefixMass_unif]



open Catalog.Novelty.KneeDilutionGrid in
theorem solution(n : ℕ) (hn : 0 < n) :
    (∀ k, collisionMass (scaled (1 / n) n) k ≤ 1 / n) ∧
      knee (scaled (1 / n) n) 1 = n ∧ (1 : ℝ) ^ 2 / (1 / n) = (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_, by field_simp⟩
  · intro k
    rw [collisionMass_scaled]
    have hmin : ((min k n : ℕ) : ℝ) ≤ n := by
      have : min k n ≤ n := Nat.min_le_right k n
      exact_mod_cast this
    have hsq : (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) * (1 / (n : ℝ)) := by ring
    rw [hsq, mul_assoc]
    have hstep : 1 / (n : ℝ) * ((min k n : ℕ) : ℝ) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one hnR]
      exact hmin
    calc 1 / (n : ℝ) * (1 / (n : ℝ) * ((min k n : ℕ) : ℝ))
        ≤ 1 / (n : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left hstep
          positivity
      _ = 1 / (n : ℝ) := by ring
  · refine knee_scaled le_rfl ?_ ?_
    · field_simp
      exact le_rfl
    · intro j hj
      have hjR : (j : ℝ) < n := by exact_mod_cast hj
      rw [div_mul_eq_mul_div, one_mul, div_lt_one hnR]
      exact hjR
