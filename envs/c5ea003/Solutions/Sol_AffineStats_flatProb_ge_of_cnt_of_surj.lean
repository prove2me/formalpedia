-- Prove2me | solution 1 for AffineStats.flatProb_ge_of_cnt_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:27.777889+00:00
-- url     : https://prove2.me/submissions/a29ea9a9-207a-4535-bab3-6094d6da410c

-- Sol generated from Applications/AffineSubspaceStats/CodimSubspace.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_card_bad_dirs_le
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the codimension-`m` lower bound construction

This file continues the development of
`Catalog/Applications/AffineSubspaceStats/AffineStats.lean`, where the model
(random affine `d`-cubes in `𝔽₂ⁿ`, the statistic `cnt`, the probability `flatProb`)
is set up, and where the codimension-one case was computed exactly
(`AffineStats.hyperplane_flatProb`).

Here we treat arbitrary codimension `m`.  Let `A ⊆ 𝔽₂ⁿ` be the codimension-`m`
subspace `{x : x₀ = ⋯ = x_{m-1} = 0}` and let `F` be a uniformly random affine
`d`-cube.  Writing `π` for the projection onto the first `m` coordinates, the cube
`y ↦ c + ∑ yᵢvᵢ` meets `A` in exactly `2^{d-m}` points as soon as the linear map
`y ↦ ∑ yᵢ π(vᵢ)` is surjective, and surjectivity fails with probability at most
`(2^m - 1)/2^d` by a union bound over the nonzero linear functionals annihilating
the image.  Consequently, with `k = d - m`,

`P[|F ∩ A| = 2^k] ≥ 1 - 2^{-k} + 2^{-d}`,

which is the standard lower-bound construction `λ*(d, 2^k) ≥ 1 - 2^{-k}` for the
affine subspace statistics problem (with an explicit improvement `2^{-d}`).

The same argument applies verbatim to a union of `j` parallel flats of codimension `m`,
i.e. to `A = π⁻¹(S)` with `|S| = j`: the cube then meets `A` in exactly `j·2^{d-m}` points,
which gives the paper's lower-bound construction `λ*(d, j·2^k) ≥ 1 - 2^{-k}`
(`AffineStats.exists_flatProb_mul_pow_two_ge`).
-/

open AffineStats

open Finset


variable {n m d : ℕ}

























open AffineStats in
theorem solution(hmn : m ≤ n) (A : Finset (Vec n)) (s : ℕ)
    (hcnt : ∀ (c : Vec n) (v : Fin d → Vec n),
      Function.Surjective (Lmap fun i => proj hmn (v i)) → cnt A c v = s) :
    1 - ((2 : ℚ) ^ m - 1) / 2 ^ d ≤ flatProb n d A s := by
  classical
  set P : (Fin d → Vec n) → Prop :=
    fun v => Function.Surjective (Lmap fun i => proj hmn (v i)) with hP
  set G := univ.filter P with hG
  set B := univ.filter fun v => ¬ P v with hB
  have hGB : G.card + B.card = 2 ^ (n * d) := by
    rw [hG, hB, Finset.card_filter_add_card_filter_not, Finset.card_univ]
    simp [ZMod.card, ← pow_mul]
  have hsubset : (univ : Finset (Vec n)) ×ˢ G ⊆ hitSet n d A s := by
    intro p hp
    simp only [Finset.mem_product, mem_univ, true_and, hG, mem_filter] at hp
    exact mem_filter.2 ⟨mem_univ _, hcnt p.1 p.2 hp⟩
  have hcard : 2 ^ n * G.card ≤ (hitSet n d A s).card := by
    have h := Finset.card_le_card hsubset
    rwa [Finset.card_product, Finset.card_univ, card_Vec] at h
  have hbad := card_bad_dirs_le (n := n) (m := m) (d := d) hmn
  rw [← hB] at hbad
  have hbadQ : (2 : ℚ) ^ d * B.card ≤ ((2 : ℚ) ^ m - 1) * 2 ^ (n * d) := by
    have h : ((2 ^ d * B.card : ℕ) : ℚ) ≤ (((2 ^ m - 1) * 2 ^ (n * d) : ℕ) : ℚ) :=
      Nat.cast_le.2 hbad
    push_cast [Nat.cast_sub (Nat.one_le_two_pow (n := m))] at h
    linarith
  have hGq : (G.card : ℚ) + B.card = 2 ^ (n * d) := by exact_mod_cast hGB
  have hnum : (2 : ℚ) ^ n * G.card ≤ ((hitSet n d A s).card : ℚ) := by
    exact_mod_cast hcard
  rw [flatProb, le_div_iff₀ (by positivity)]
  have hden : (2 : ℚ) ^ (n * (d + 1)) = 2 ^ n * 2 ^ (n * d) := by
    rw [← pow_add]; ring_nf
  rw [hden]
  set t : ℚ := ((2 : ℚ) ^ m - 1) / 2 ^ d with ht
  have htd : t * 2 ^ d = (2 : ℚ) ^ m - 1 := by
    rw [ht, div_mul_cancel₀ _ (by positivity : ((2 : ℚ) ^ d) ≠ 0)]
  have hBt : (B.card : ℚ) ≤ t * 2 ^ (n * d) := by
    have hd : (0 : ℚ) < 2 ^ d := by positivity
    rw [← htd] at hbadQ
    nlinarith [hbadQ]
  have h2n : (0 : ℚ) < 2 ^ n := by positivity
  nlinarith [hnum, hGq, hBt, h2n]
