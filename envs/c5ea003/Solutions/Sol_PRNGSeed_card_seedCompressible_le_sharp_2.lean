-- Prove2me | solution 2 for PRNGSeed.card_seedCompressible_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:22:57.327961+00:00
-- url     : https://prove2.me/submissions/12145b6f-e1ad-456f-a37f-673f99c8c2b6

/-
# `PRNGSeed.card_seedCompressible_le_sharp`
Target `e26c6137` (Open; re-read live immediately before submitting).

ORDINARY PROOF — full closure screens CLEAN (five bundles, no `Theorems.` import). Gift: **SAFE**,
and it is the LEAF: proving it voids `e1bc49b4 lfsrRun_zero_seed`'s gift.

BINDERS. History is `SKETCH_ACCEPTED` only — **no WA has ever published an expected type here**, so
unlike its siblings the telescope is read off the statement text alone: `(N L : ℕ)`, both explicit,
no `F` (everything is over `Bool`).

DEFINITIONS:
    Bits N                   = Fin N → Bool
    lfsrBits L c init n      = ofZ2 (lfsrRun (toZ2 ∘ c) (toZ2 ∘ init) n)
    IsSeedCompressible N L w = ∃ c init : Fin L → Bool, ∀ i : Fin N, w i = lfsrBits L c init i
    seedCompressibleFinset N L = univ.filter (IsSeedCompressible N L ·)

WHY THE BOUND IS "SHARP". A compressible word is determined by a (taps, seed) pair, and there are
`2^L · 2^L = 4^L` pairs — so `4^L` is the obvious bound. It is not tight: **every pair whose seed is
all-zero produces the same word**, the zero word, whatever the taps. That collapses `2^L` pairs to a
single image point, losing `2^L - 1`, giving `4^L - 2^L + 1`. The statement is that rearranged to
avoid ℕ-subtraction: `card + 2^L ≤ 4^L + 1`.

The zero-seed fact is `lfsrRun_zero_seed` (target `e1bc49b4`) — which is exactly why that target
GIFTS this one, and why this must ship first. It is RE-DERIVED INLINE; importing from `Theorems/`
would force the reduction path and an axiom audit.

PROBED, NOT GUESSED — all READ from source:
  * `Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β]` — Data/Fintype/BigOperators.lean:199
  * `Finset.card_image_le : #(s.image f) ≤ #s`                 — Data/Finset/Card.lean:225
  * `Finset.card_image_of_injective` / `card_image_of_injOn`   — Card.lean:231
  * `Finset.card_insert_le (a) (s) : #(insert a s) ≤ #s + 1`   — Card.lean
  * `Finset.card_le_card : s ⊆ t → #s ≤ #t`                     — Card.lean
  * `lfsrRun` is WELL-FOUNDED; `rw [lfsrRun.eq_def]` works (four-candidate probe).
  * the zero-seed induction is stated over a GENERIC all-false seed `s` rather than the literal
    `fun _ => false`, so no beta-reduction mismatch can block the rewrite.
-/
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGSeedDetection
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR

set_option autoImplicit false
set_option maxHeartbeats 1000000

open PRNGSeed PRNGCompression Finset

open PRNGSeed PRNGCompression in
/-- **The target, verbatim.** -/
theorem solution (N L : ℕ) :
    (seedCompressibleFinset N L).card + 2 ^ L ≤ 4 ^ L + 1 := by
  classical
  -- (1) zero seed ⇒ zero run, whatever the taps  (this is `lfsrRun_zero_seed`, inlined)
  have hzs : ∀ (c s : Fin L → Bool), (∀ i, s i = false) → ∀ n : ℕ,
      lfsrRun (fun i => toZ2 (c i)) (fun i => toZ2 (s i)) n = 0 := by
    intro c s hs n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [lfsrRun.eq_def]
      by_cases h : n < L
      · rw [dif_pos h]
        simp [hs, toZ2]
      · rw [dif_neg h]
        have hterm : ∀ i : Fin L,
            toZ2 (c i) * lfsrRun (fun j => toZ2 (c j)) (fun j => toZ2 (s j)) (n - L + (i : ℕ)) = 0 := by
          intro i
          have hi := i.isLt
          have hlt : n - L + (i : ℕ) < n := by omega
          rw [ih _ hlt, mul_zero]
        simp [hterm]
  -- (2) the map from (taps, seed) pairs to words
  set G : (Fin L → Bool) × (Fin L → Bool) → Bits N :=
    fun cs => fun i => lfsrBits L cs.1 cs.2 (i : ℕ) with hGdef
  set zw : Bits N := fun _ => false with hzwdef
  have hGzero : ∀ c : Fin L → Bool, G (c, fun _ => false) = zw := by
    intro c
    funext i
    show lfsrBits L c (fun _ => false) (i : ℕ) = false
    rw [lfsrBits, hzs c (fun _ => false) (fun _ => rfl) (i : ℕ)]
    simp [ofZ2]
  -- (3) every compressible word is in the image of G
  have hsub : seedCompressibleFinset N L ⊆ Finset.image G Finset.univ := by
    intro w hw
    rw [seedCompressibleFinset, Finset.mem_filter] at hw
    obtain ⟨c, init, hci⟩ := hw.2
    refine Finset.mem_image.mpr ⟨(c, init), Finset.mem_univ _, ?_⟩
    funext i
    exact (hci i).symm
  -- (4) the zero-seed pairs, and their cardinality
  set Z : Finset ((Fin L → Bool) × (Fin L → Bool)) :=
    Finset.image (fun c : Fin L → Bool => (c, (fun _ => false : Fin L → Bool))) Finset.univ with hZdef
  have hinj : Function.Injective
      (fun c : Fin L → Bool => (c, (fun _ => false : Fin L → Bool))) := by
    intro a b hab
    exact (Prod.mk.injEq _ _ _ _ ▸ hab).1
  have hcardBool : Fintype.card (Fin L → Bool) = 2 ^ L := by
    simp [Fintype.card_fun]
  have hcardZ : Z.card = 2 ^ L := by
    rw [hZdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, hcardBool]
  have hcardU : (Finset.univ : Finset ((Fin L → Bool) × (Fin L → Bool))).card = 4 ^ L := by
    rw [Finset.card_univ, Fintype.card_prod, hcardBool]
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
  -- (5) the image lands inside `insert zw (image G (univ \ Z))`
  have himg : Finset.image G Finset.univ ⊆ insert zw (Finset.image G (Finset.univ \ Z)) := by
    intro w hw
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hw
    by_cases hz : x.2 = fun _ => false
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      rw [← hx]
      have : x = (x.1, fun _ => false) := Prod.ext rfl hz
      rw [this, hGzero]
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      refine Finset.mem_image.mpr ⟨x, ?_, hx⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hmem
      exact hz (by rw [← hc])
  -- (6) chain the cardinalities
  have hZsub : Z ⊆ (Finset.univ : Finset ((Fin L → Bool) × (Fin L → Bool))) :=
    Finset.subset_univ _
  -- stated stepwise: hand-threaded `le_trans` left `Finset.card_image_le`'s implicits unsolved
  -- ("Function expected at"), because nothing in that position fixed `s` and `f`.
  have hA : (seedCompressibleFinset N L).card ≤ (Finset.image G Finset.univ).card :=
    Finset.card_le_card hsub
  have hB : (Finset.image G Finset.univ).card
      ≤ (insert zw (Finset.image G (Finset.univ \ Z))).card :=
    Finset.card_le_card himg
  have hC : (insert zw (Finset.image G (Finset.univ \ Z))).card
      ≤ (Finset.image G (Finset.univ \ Z)).card + 1 :=
    Finset.card_insert_le _ _
  have hD : (Finset.image G (Finset.univ \ Z)).card ≤ (Finset.univ \ Z).card :=
    Finset.card_image_le
  have h1 : (seedCompressibleFinset N L).card ≤ (Finset.univ \ Z).card + 1 :=
    hA.trans (hB.trans (hC.trans (Nat.add_le_add_right hD 1)))
  have h2 : (Finset.univ \ Z).card = 4 ^ L - 2 ^ L := by
    -- `Finset.card_sdiff` here is UNCONDITIONAL: #(s \ t) = #s - #(t ∩ s). Passing the
    -- subset proof `hZsub` gave "Function expected at card_sdiff". Discharge `Z ∩ univ = Z`.
    rw [Finset.card_sdiff, Finset.inter_univ, hcardU, hcardZ]
  have h3 : 2 ^ L ≤ 4 ^ L := Nat.pow_le_pow_left (by norm_num) L
  rw [h2] at h1
  omega
