-- Prove2me | solution 1 for QubitTrade.card_levelRecords
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:21:25.451663+00:00
-- url     : https://prove2.me/submissions/df4ab8c2-6587-4114-9f56-358c933dd551

-- Sol generated from Algebra/QubitTrade/JordanCount.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_JordanCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SuccessDensity
import Theorems.Thm_QubitTrade_recordGcd_dvd_mem
import Theorems.Thm_QubitTrade_recordGcd_map_div

/-!
# QUBIT-TRADE XII: the exact number of successful records

`SuccessDensity.lean` bounds the number of *good* records — the length-`m`
records of numerators whose joint gcd is coprime to the order `r`, i.e. exactly
the records that `recordEstimate` turns into the true order — from below by
`r^m / 2`.  Here we compute that number **exactly**.

The count is Jordan's totient `J_m(r)`:

* `QubitTrade.sum_card_goodRecords` — the divisor identity
  `∑_{d ∣ r} #good(d, m) = r^m`, proved by an explicit bijection that rescales a
  record by the gcd of its entries with `r`;
* `QubitTrade.card_goodRecords_eq_moebius_sum` — Möbius inversion of that
  identity: `#good(r, m) = ∑_{d ∣ r} μ(d) · (r/d)^m`;
* `QubitTrade.card_goodRecords_eq_euler_product` — the closed Euler product
  `#good(r, m) = r^m · ∏_{p ∣ r} (1 − p^{−m})`.

The last statement is the exact form of the success density conjectured in the
previous cycle: the failure probability of an `m`-sample record is exactly
`1 − ∏_{p ∣ r} (1 − p^{−m})`, which is `≤ ω(r)·2^{−m}` and `< 1/2` for `m ≥ 2`,
recovering the earlier bounds and pinning the constant.
-/

open QubitTrade

open Finset ArithmeticFunction

variable {r m : ℕ}

/-! ## Rescaling records -/


/-- Multiplying every entry of a record by `e` multiplies its gcd by `e`. -/
theorem recordGcd_map_mul {e : ℕ} :
    ∀ L : List ℕ, recordGcd (L.map (fun x => e * x)) = e * recordGcd L := by
  intro L
  induction L with
  | nil => simp [recordGcd]
  | cons a L ih =>
      have h1 : recordGcd ((a :: L).map (fun x => e * x))
          = Nat.gcd (e * a) (recordGcd (L.map (fun x => e * x))) := by
        simp [recordGcd]
      have h2 : recordGcd (a :: L) = Nat.gcd a (recordGcd L) := by simp [recordGcd]
      rw [h1, ih, h2, Nat.gcd_mul_left]


theorem mem_levelRecords {n e : ℕ} {f : Fin m → ℕ} :
    f ∈ levelRecords n m e ↔
      (∀ i, f i < n) ∧ Nat.gcd (recordGcd (List.ofFn f)) n = e := by
  simp [levelRecords, allRecords, Fintype.mem_piFinset]





/-! ## The Euler product -/




open QubitTrade in
theorem solution{n e : ℕ} (hn : 0 < n) (he : e ∣ n) :
    (levelRecords n m e).card = (goodRecords (n / e) m).card := by
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hn
  refine Finset.card_bij' (fun f _ => fun i => f i / e) (fun g _ => fun i => e * g i)
    ?_ ?_ ?_ ?_
  · -- forward maps into `goodRecords (n / e) m`
    intro f hf
    rw [mem_levelRecords] at hf
    obtain ⟨hlt, hgcd⟩ := hf
    have hdvd : ∀ i, e ∣ f i := by
      intro i
      have h1 : e ∣ recordGcd (List.ofFn f) := hgcd ▸ Nat.gcd_dvd_left _ _
      exact h1.trans (recordGcd_dvd_mem (List.mem_ofFn.mpr ⟨i, rfl⟩))
    have hmapeq : List.ofFn (fun i => f i / e)
        = (List.ofFn f).map (fun x => x / e) := by
      simp [List.map_ofFn, Function.comp_def]
    have hgcd' : recordGcd (List.ofFn (fun i => f i / e)) * e = recordGcd (List.ofFn f) := by
      rw [hmapeq]
      exact recordGcd_map_div (fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact hdvd i)
    have hkey : recordGcd (List.ofFn (fun i => f i / e)) = recordGcd (List.ofFn f) / e := by
      rw [← hgcd', Nat.mul_div_cancel _ hepos]
    simp only [goodRecords, allRecords, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_range]
    refine ⟨fun i => Nat.div_lt_div_of_lt_of_dvd he (hlt i), ?_⟩
    rw [hkey, ← hgcd]
    exact Nat.coprime_div_gcd_div_gcd (by omega)
  · -- backward maps into `levelRecords n m e`
    intro g hg
    simp only [goodRecords, allRecords, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_range] at hg
    obtain ⟨hlt, hcop⟩ := hg
    rw [mem_levelRecords]
    constructor
    · intro i
      have := hlt i
      calc e * g i < e * (n / e) := by
            exact mul_lt_mul_of_pos_left this hepos
        _ = n := Nat.mul_div_cancel' he
    · have hmapeq : List.ofFn (fun i => e * g i) = (List.ofFn g).map (fun x => e * x) := by
        simp [List.map_ofFn, Function.comp_def]
      rw [hmapeq, recordGcd_map_mul]
      calc Nat.gcd (e * recordGcd (List.ofFn g)) n
          = Nat.gcd (e * recordGcd (List.ofFn g)) (e * (n / e)) := by
            rw [Nat.mul_div_cancel' he]
        _ = e * Nat.gcd (recordGcd (List.ofFn g)) (n / e) := Nat.gcd_mul_left _ _ _
        _ = e := by rw [hcop, mul_one]
  · intro f hf
    rw [mem_levelRecords] at hf
    obtain ⟨-, hgcd⟩ := hf
    funext i
    have h1 : e ∣ recordGcd (List.ofFn f) := hgcd ▸ Nat.gcd_dvd_left _ _
    exact Nat.mul_div_cancel' (h1.trans (recordGcd_dvd_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  · intro g _
    funext i
    exact Nat.mul_div_cancel_left _ hepos
