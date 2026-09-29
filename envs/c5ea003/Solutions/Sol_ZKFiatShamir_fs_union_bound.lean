-- Prove2me | solution 1 for ZKFiatShamir.fs_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:10:28.243751+00:00
-- url     : https://prove2.me/submissions/c16ae7b6-0a93-45b8-89ee-48ca4f0c75cb

-- Sol generated from Shared/ZeroKnowledge/NIZKFiatShamir.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_NIZKFiatShamir
import Theorems.Thm_ZKFiatShamir_hashHits_card_mul

/-!
# Non-interactive zero knowledge: the Fiat–Shamir transform in the random-oracle model

An interactive `Σ`-protocol (commit `a`, random challenge `c`, response `r`) is made
*non-interactive* by replacing the verifier's coin flips with the value `H a` of a hash
function. In the random-oracle model the hash function is drawn uniformly from the finite
set of *all* functions `Msg → Chal`, and this file carries out the resulting exact
counting.

## Main results

* `fiber_card_const` — for a fixed query `a`, all the fibers `{H | H a = c}` have the same
  size. Equivalently: *the value of a random oracle at a point is uniformly distributed*,
  and reprogramming the oracle at one point is undetectable — the counting fact behind
  zero knowledge of the transformed protocol.
* `fiber_prob` — the probability that a uniform oracle sends `a` to a fixed challenge is
  exactly `1/|Chal|`.
* `hashHits_card_mul` and `fsError_eq` — the probability that `H a` lands in a set `B` of
  bad challenges is exactly `|B|/|Chal|`, i.e. Fiat–Shamir with a single fixed first
  message inherits the soundness error of the interactive protocol.
* `fs_union_bound` — a cheating prover that may try any first message from a set `A₀`
  succeeds with probability at most `|A₀| · d / |Chal|`, where `d` bounds the number of
  answerable challenges.
* `SigmaProtocol.fiat_shamir_soundness` — the same statement for a `d`-special-sound
  `Σ`-protocol on a false statement: the non-interactive proof system is sound with error
  `|A₀| · d / |Chal|`.
-/

open Finset

open ZKFiatShamir

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

/-! ## Random oracles: exact fiber counting -/






/-! ## Soundness of the Fiat–Shamir transform -/




/-- **The transform preserves the soundness error exactly**: the probability that a
uniform oracle produces a challenge in `B` equals `|B|/|Chal|`, the acceptance probability
of the interactive protocol on the bad challenge set `B`. -/
theorem fsError_eq [Nonempty C] (a : A) (B : Finset C) :
    fsError a B = (B.card : ℝ) / Fintype.card C := by
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty C›
  have hAC : (0 : ℝ) < Fintype.card (A → C) := by
    have : Nonempty (A → C) := ⟨fun _ => Classical.arbitrary C⟩
    exact_mod_cast Fintype.card_pos_iff.mpr this
  have h : ((hashHits a B).card : ℝ) * Fintype.card C = B.card * Fintype.card (A → C) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (hashHits_card_mul a B)
  rw [fsError]
  field_simp
  linarith [h]

/-- If at most `d` challenges are answerable, the transformed protocol has soundness error
at most `d/|Chal|` per first message. -/
theorem fsError_le [Nonempty C] (a : A) (B : Finset C) (d : ℕ) (h : B.card ≤ d) :
    fsError a B ≤ (d : ℝ) / Fintype.card C := by
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty C›
  rw [fsError_eq]
  gcongr


/-! ## Application to `Σ`-protocols -/


variable {Stmt Msg Resp : Type*}






open ZKFiatShamir in
theorem solution[Nonempty C] (A₀ : Finset A) (bad : A → Finset C) (d : ℕ)
    (hd : ∀ a, (bad a).card ≤ d) :
    ((univ.filter fun H : A → C => ∃ a ∈ A₀, H a ∈ bad a).card : ℝ) / Fintype.card (A → C)
      ≤ (A₀.card : ℝ) * d / Fintype.card C := by
  classical
  have hAC : (0 : ℝ) < Fintype.card (A → C) := by
    have : Nonempty (A → C) := ⟨fun _ => Classical.arbitrary C⟩
    exact_mod_cast Fintype.card_pos_iff.mpr this
  have hsub : (univ.filter fun H : A → C => ∃ a ∈ A₀, H a ∈ bad a)
      ⊆ A₀.biUnion fun a => hashHits a (bad a) := by
    intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    obtain ⟨a, ha, hab⟩ := hH
    exact mem_biUnion.mpr ⟨a, ha, by simpa [hashHits] using hab⟩
  have hcard : ((univ.filter fun H : A → C => ∃ a ∈ A₀, H a ∈ bad a).card : ℝ)
      ≤ ∑ a ∈ A₀, ((hashHits a (bad a)).card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := A₀) (t := fun a => hashHits a (bad a))
    have : (univ.filter fun H : A → C => ∃ a ∈ A₀, H a ∈ bad a).card
        ≤ ∑ a ∈ A₀, (hashHits a (bad a)).card := le_trans h1 h2
    exact_mod_cast this
  calc ((univ.filter fun H : A → C => ∃ a ∈ A₀, H a ∈ bad a).card : ℝ) / Fintype.card (A → C)
      ≤ (∑ a ∈ A₀, ((hashHits a (bad a)).card : ℝ)) / Fintype.card (A → C) := by
        gcongr
    _ = ∑ a ∈ A₀, fsError a (bad a) := by
        rw [Finset.sum_div]
        rfl
    _ ≤ ∑ _a ∈ A₀, (d : ℝ) / Fintype.card C :=
        Finset.sum_le_sum fun a _ => fsError_le a (bad a) d (hd a)
    _ = (A₀.card : ℝ) * d / Fintype.card C := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
