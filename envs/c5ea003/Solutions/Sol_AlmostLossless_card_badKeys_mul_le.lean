-- Prove2me | solution 1 for AlmostLossless.card_badKeys_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T10:42:26.993169+00:00
-- url     : https://prove2.me/submissions/6dae0de6-b6ee-429f-b5ad-b33c40cc428a

/-
# `AlmostLossless.card_badKeys_mul_le`
Target `5d487cd9` (Open; re-read live immediately before submitting).

ORDINARY PROOF — closure screens CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries six):
    ∀ {α : Type} [DecidableEq α] {K M : ℕ} {H : Fin K → α → Fin M},
      Universal2 H → ∀ (S : Finset α) (x : α),
        ↑(badKeys H S x).card * ↑M ≤ ↑K * ↑S.card
`[DecidableEq α]` but **NO `[Fintype α]`** — `badKeys` filters `Finset.univ : Finset (Fin K)`, whose
finiteness comes from `Fin K`, never from `α`. `hU` is explicit; `S` and `x` explicit.

DEFINITIONS (read from source):
    Universal2 H       = ∀ x y, x ≠ y → ((univ.filter fun k => H k x = H k y).card : ℝ) * M ≤ K
    collisionSet H k S x = (S.erase x).filter (fun y => H k y = H k x)
    Collides H k S x   = (collisionSet H k S x).Nonempty
    badKeys H S x      = univ.filter (fun k => Collides H k S x)

MATHS — a union bound. A key is bad exactly when SOME other codebook entry shares `x`'s bucket, so
    badKeys H S x ⊆ (S.erase x).biUnion (fun y => univ.filter fun k => H k y = H k x)
and `card_biUnion_le` bounds the union by the sum. Universality bounds each summand:
`(card {k | H k y = H k x} : ℝ) * M ≤ K` for every `y ≠ x`. Summing over `S.erase x` gives
`card(badKeys) * M ≤ card(S.erase x) * K ≤ card S * K`.

TWO POINTS OF CARE, both found by READING rather than assuming:
  * `Universal2` is stated as `H k x = H k y` while `collisionSet` filters on `H k y = H k x`. The
    two filters differ by `eq_comm` and the sets must be reconciled explicitly — they are not
    syntactically equal.
  * `Universal2` already carries the multiplication in ℝ (stated multiplicatively "to avoid
    division"), so the whole chain is assembled in ℝ; the ℕ-level cardinality bound is cast once,
    up front, rather than at the end.

PROBED, NOT GUESSED — all READ from Mathlib source:
  * `Finset.card_biUnion_le {s} {t} : #(s.biUnion t) ≤ ∑ a ∈ s, #(t a)` — BigOperators/.../Basic:971
  * `Finset.subset_biUnion_of_mem (u) {x} (xs : x ∈ s) : u x ⊆ s.biUnion u` — Data/Finset/Union:243
  * `Finset.mem_biUnion : b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a` — Data/Finset/Union:200
  * `Finset.card_erase_le : #(s.erase a) ≤ #s` — Data/Finset/Card:162
  * `Nat.cast_le : (m : α) ≤ n ↔ m ≤ n` — Data/Nat/Cast/Order/Basic:76
-/
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding

set_option autoImplicit false
set_option maxHeartbeats 800000

open AlmostLossless Finset

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {α : Type*} [DecidableEq α] {K M : ℕ} {H : Fin K → α → Fin M}
    (hU : Universal2 H) (S : Finset α) (x : α) :
    ((badKeys H S x).card : ℝ) * M ≤ (K : ℝ) * S.card := by
  classical
  set T : α → Finset (Fin K) := fun y => Finset.univ.filter (fun k => H k y = H k x) with hT
  -- a bad key lies in the union of the per-entry collision key-sets
  have hsub : badKeys H S x ⊆ (S.erase x).biUnion T := by
    intro k hk
    simp only [badKeys, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨y, hy⟩ := hk
    simp only [collisionSet, Finset.mem_filter] at hy
    refine Finset.mem_biUnion.mpr ⟨y, hy.1, ?_⟩
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hy.2
  -- ℕ-level union bound
  have hcard : (badKeys H S x).card ≤ ∑ y ∈ S.erase x, (T y).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcardR : ((badKeys H S x).card : ℝ) ≤ ∑ y ∈ S.erase x, ((T y).card : ℝ) := by
    exact_mod_cast hcard
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- universality bounds each summand, after reconciling the direction of the equation
  have hterm : ∀ y ∈ S.erase x, ((T y).card : ℝ) * M ≤ (K : ℝ) := by
    intro y hy
    have hyx : y ≠ x := Finset.ne_of_mem_erase hy
    have hswap : T y = Finset.univ.filter (fun k => H k x = H k y) := by
      simp only [hT]
      exact Finset.filter_congr (fun k _ => by constructor <;> exact fun h => h.symm)
    rw [hswap]
    exact hU x y (Ne.symm hyx)
  calc ((badKeys H S x).card : ℝ) * M
      ≤ (∑ y ∈ S.erase x, ((T y).card : ℝ)) * M := by
        exact mul_le_mul_of_nonneg_right hcardR hM
    _ = ∑ y ∈ S.erase x, ((T y).card : ℝ) * M := by rw [Finset.sum_mul]
    _ ≤ ∑ _y ∈ S.erase x, (K : ℝ) := Finset.sum_le_sum hterm
    _ = ((S.erase x).card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ) * K := by
        have : ((S.erase x).card : ℝ) ≤ (S.card : ℝ) := by
          exact_mod_cast Finset.card_erase_le
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg K)
    _ = (K : ℝ) * S.card := by ring
