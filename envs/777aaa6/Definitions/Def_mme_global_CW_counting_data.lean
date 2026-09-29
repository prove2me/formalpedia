-- Prove2me | Definitions.Def_mme_global_CW_counting_data
-- name    : mme_global_CW_counting_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T07:43:23.796802+00:00
-- url     : https://prove2.me/theorems/9782e4ea-e52e-4420-ac4a-61e1e88b6973
-- title:
--   Exact global mode profiles and usable hash states
-- statement:
--   Exact mode histograms of words on unpaired global CW blocks, their multinomial counts, compatible-competitor holes under common-label hashing, and the usable-address predicate. These definitions contain no assumed counting estimate.
-- source:
--   More Asymmetry Proposition 5.1 / Theorem 5.3: finite global extraction interface.

import Definitions.Def_mme_global_CW_stage_data
import Definitions.Def_mme_recursive_yz_hash_filter
open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
namespace MME.GlobalCW
noncomputable def ModeType {degree R : ℕ} {n : Fin R → ℕ} {W : Type*}
    (y : ∀ r, Fin (n r) → Fin (degree + 1))
    (eta : Fin R → Fin (degree + 1) → W → ℕ) (f : Place n → W) : Prop :=
  ∀ r, Useful (y r) (eta r) (fun t ↦ f ⟨r,t⟩)

noncomputable def aggregate {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {W : Type*}
    (i : Fin 3) (mu : Cell degree R bounds → W → ℕ)
    (r : Fin R) (j : Fin (degree + 1)) (w : W) : ℕ := by
  classical
  exact ∑ c, if modeGroup i c = (r,j) then mu c w else 0

noncomputable def modeNumber {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (i : Fin 3) (mu : Cell degree R bounds → W → ℕ) : ℕ :=
  histogramNumber (fun g : Fin R × Fin (degree+1) ↦ aggregate i mu g.1 g.2)

noncomputable def ambiguous {degree R ell N p : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p))
    (state : (Fin (N+2) → ZMod p) × ZMod p) (i : Fin 2)
    (mu : Cell degree R bounds → CompleteSplit.CompleteWord ell → ℕ)
    (a : RecursiveXHash.Address degree R bounds n) (f : Place n → CompleteSplit.CompleteWord ell) : Prop :=
  ∃ b ∈ RecursiveXHash.target m,
    RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a ∧
    Compatible (cell b) (yzBoundary i) (modeGroup (yzMode i)) mu f ∧
    b ≠ a ∧ b ∈ RecursiveXHash.hashed m e S state

noncomputable def hashHoles {degree R ell N p : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p))
    (state : (Fin (N+2) → ZMod p) × ZMod p) (i : Fin 2)
    (mu : Cell degree R bounds → CompleteSplit.CompleteWord ell → ℕ)
    (a : RecursiveXHash.Address degree R bounds n) : Finset (Place n → CompleteSplit.CompleteWord ell) := by
  classical
  exact (words (yzMode i) a mu).filter (ambiguous m e S state i mu a)

noncomputable def hashUsable {degree R ell N p : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p))
    (state : (Fin (N+2) → ZMod p) × ZMod p) (d : ℕ)
    (mu : Fin 3 → Cell degree R bounds → CompleteSplit.CompleteWord ell → ℕ) :
    Finset (RecursiveXHash.Address degree R bounds n) := by
  classical
  exact (RecursiveXHash.target m).filter (fun a ↦ ∀ i : Fin 2,
    4 * d * (hashHoles m e S state i (mu (yzMode i)) a).card ≤
      (words (yzMode i) a (mu (yzMode i))).card)
end MME.GlobalCW


