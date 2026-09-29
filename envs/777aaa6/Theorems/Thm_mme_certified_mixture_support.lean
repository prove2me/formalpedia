-- Prove2me | Theorems.Thm_mme_certified_mixture_support
-- name    : mme_certified_mixture_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:29:17.519068+00:00
-- url     : https://prove2.me/theorems/eb0efa2b-f89f-4990-9bf8-88a69bb3b641
-- title:
--   A parent mixture vanishes at word pairs no split can produce
-- statement:
--   A parent mixture vanishes at any pair of words that no split can produce.
--
--   A cell frequency is zero wherever its profile is, and the mixture of a region is a weighted sum over
--   its splits of the product of two such frequencies. So if for every split at least one of the two
--   words is absent from the relevant cell, the whole mixture vanishes there.
--
--   Together with the fact that a certified floor only sees the support of its distribution, this is
--   what keeps the cost of certifying a mixture proportional to the words it actually uses rather than
--   to the size of the alphabet.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_thin_split_data
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

theorem mme_certified_mixture_support :
    (∀ {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W),
      mu c w = 0 → freqQ mu c w = 0) ∧
    ∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W),
      (∀ c, mu ⟨r, c⟩ (w 0) = 0 ∨ mu ⟨r, complement (htotal r) c⟩ (w 1) = 0) →
      mixQ htotal n m mu r w = 0 := by sorry
