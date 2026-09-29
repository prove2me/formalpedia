-- Prove2me | solution 1 for ZKFiatShamir.hashHits_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:08:47.923214+00:00
-- url     : https://prove2.me/submissions/be9460ed-64b6-46c4-9bd7-0e8f1d521f3c

-- Sol generated from Shared/ZeroKnowledge/NIZKFiatShamir.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_NIZKFiatShamir

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


/-- **Reprogramming a random oracle at one point is undetectable**: all fibers over a
fixed query have the same cardinality. -/
theorem fiber_card_const (a : A) (c₁ c₂ : C) : (fiber a c₁).card = (fiber a c₂).card := by
  apply Finset.card_nbij' (fun H => Function.update H a c₂) (fun H => Function.update H a c₁)
    <;> intro H hH <;> simp_all [fiber, funext_iff, Function.update_apply]

/-- The fibers over a fixed query partition the space of oracles. -/
theorem sum_fiber_card (a : A) : ∑ c : C, (fiber a c).card = Fintype.card (A → C) := by
  simp only [fiber]
  rw [← Finset.card_univ (α := A → C)]
  exact (Finset.card_eq_sum_card_fiberwise fun H _ => mem_univ (H a)).symm

/-- Exact uniformity: `|{H | H a = c}| · |Chal| = |Msg → Chal|`. -/
theorem fiber_card_mul (a : A) (c : C) :
    (fiber a c).card * Fintype.card C = Fintype.card (A → C) := by
  rw [← sum_fiber_card a, Finset.sum_congr rfl fun c' _ => fiber_card_const a c' c,
    Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_comm]


/-! ## Soundness of the Fiat–Shamir transform -/







/-! ## Application to `Σ`-protocols -/


variable {Stmt Msg Resp : Type*}






open ZKFiatShamir in
theorem solution(a : A) (B : Finset C) :
    (hashHits a B).card * Fintype.card C = B.card * Fintype.card (A → C) := by
  have hsplit : (hashHits a B).card = ∑ c ∈ B, (fiber a c).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun H : A → C => H a) (s := hashHits a B) (t := B)
      (fun H hH => by simpa [hashHits] using hH)
    refine h.trans (Finset.sum_congr rfl fun c hc => ?_)
    congr 1
    ext H
    simp only [hashHits, mem_filter, mem_univ, true_and, fiber]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hc, h⟩⟩
  rcases B.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · simp [hsplit]
  · have hconst : ∑ c ∈ B, (fiber a c).card = B.card * (fiber a c₀).card := by
      rw [Finset.sum_congr rfl fun c _ => fiber_card_const a c c₀]
      simp
    rw [hsplit, hconst, mul_assoc, fiber_card_mul a c₀]
