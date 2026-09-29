-- Prove2me | Definitions.Def_mme_recursive_region_parent_profiles
-- name    : mme_recursive_region_parent_profiles
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T16:59:42.217251+00:00
-- url     : https://prove2.me/theorems/cce94dac-3436-40d4-bea3-b7e1be011578
-- title:
--   The fixed product-mixture parent profile of a region
-- statement:
--   Define exact cell frequencies, their complementary-child mixture weighted by joint split counts, and the parent tolerance predicate. The center is determined by integer data and does not depend on the selected target address.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Definitions.Def_mme_recursive_yz_physical_words
import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Real.Basic

open BigOperators MME MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
namespace MME.RegionRealization

noncomputable def cellFrequency {C W : Type*} [Fintype W]
    (mu : C → W → ℕ) (c : C) (w : W) : ℝ :=
  (mu c w : ℝ) / ((∑ v, mu c v : ℕ) : ℝ)

/-- The parent distribution is the prescribed mixture of products of its two
child-cell distributions. It is independent of the chosen target address. -/
noncomputable def parentMixture {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W) : ℝ :=
  (∑ c, (m r c : ℝ) * cellFrequency mu ⟨r,c⟩ (w 0) *
    cellFrequency mu ⟨r,complement (htotal r) c⟩ (w 1)) / n r

/-- Every joint parent-word frequency is within epsilon of the fixed mixture. -/
noncomputable def parentTypical {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (eps : ℝ) (f : Position n → W) : Prop :=
  ∀ r w, |(Fintype.card {t : Fin (n r) // ∀ h, f ⟨r,t,h⟩ = w h} : ℝ) / n r -
    parentMixture htotal n m mu r w| < eps

end MME.RegionRealization


