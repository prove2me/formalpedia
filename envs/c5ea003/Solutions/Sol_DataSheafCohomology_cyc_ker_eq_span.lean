-- Prove2me | solution 1 for DataSheafCohomology.cyc_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:36:38.730982+00:00
-- url     : https://prove2.me/submissions/a2e165af-d3fe-4ad5-8ea6-5f561df65f43

import Mathlib
import Definitions.Def_Algebra_DataSheafCohomology
open DataSheafCohomology Finset in
theorem solution {K : Type*} [Field K] {m : ℕ} {a : ℕ → K} (ha : ∀ j, j < m + 1 → a j ≠ 0)
    (hh : holonomy a m = 1) :
    LinearMap.ker (cycD m a) = K ∙ (cycSection a m) := by
  -- the canonical section is a cocycle
  have hstep : ∀ i : Fin (m+1), a i.val * cycSection a m (i + 1) = cycSection a m i := by
    intro i
    simp only [cycSection]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 i.isLt) with hi | hi
    · -- interior step: one more factor `a i` in the transported product
      have hv : ((i + 1 : Fin (m+1)) : ℕ) = i.val + 1 :=
        Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hi)
      rw [hv, prod_range_succ, mul_inv, mul_left_comm, mul_inv_cancel₀ (ha _ (by omega)), mul_one]
    · -- wrap-around step: trivial holonomy closes the loop
      have hil : i = Fin.last m := Fin.ext (by rw [Fin.val_last]; exact hi)
      subst hil
      rw [Fin.last_add_one, Fin.val_zero, prod_range_zero, inv_one, mul_one, Fin.val_last]
      unfold holonomy at hh
      rw [prod_range_succ] at hh
      exact eq_inv_of_mul_eq_one_right hh
  have hcyc : ∀ (f : Fin (m+1) → K) (i : Fin (m+1)), cycD m a f i = a i.val * f (i + 1) - f i :=
    fun f i => rfl
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hf
    have hrel : ∀ i : Fin (m+1), a i.val * f (i + 1) = f i := by
      intro i
      have := congrFun hf i
      rw [hcyc] at this
      exact sub_eq_zero.mp this
    -- a cocycle is determined by its value at `0`
    have key : ∀ n (hn : n < m + 1), f 0 * (∏ j ∈ range n, a j)⁻¹ = f ⟨n, hn⟩ := by
      intro n
      induction n with
      | zero =>
        intro hn
        rw [prod_range_zero, inv_one, mul_one]
        rfl
      | succ n ih =>
        intro hn
        have hv : ((⟨n, by omega⟩ : Fin (m+1)) + 1) = ⟨n + 1, hn⟩ :=
          Fin.ext (Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; show n < m; omega))
        have hi : a n * f ((⟨n, by omega⟩ : Fin (m+1)) + 1) = f ⟨n, by omega⟩ := hrel ⟨n, by omega⟩
        rw [hv, ← ih (by omega)] at hi
        rw [prod_range_succ, mul_inv, ← mul_assoc, ← hi, mul_comm (a n), mul_assoc,
          mul_inv_cancel₀ (ha n (by omega)), mul_one]
    refine ⟨f 0, ?_⟩
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, cycSection]
    exact key k.val k.isLt
  · rintro ⟨c, rfl⟩
    rw [map_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [hcyc, hstep, sub_self, mul_zero]
