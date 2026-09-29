-- Prove2me | solution 1 for OperatorAlgebraicDL.contractive_convergence_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:16:13.414228+00:00
-- url     : https://prove2.me/submissions/a81a1e6f-859d-4b15-b40d-dbf17fbd7319

import Mathlib
import Definitions.Def_Bridges_WeightAlgebra
open OperatorAlgebraicDL Finset Real in
theorem solution {A : Type*} [NormedRing A] [NormOneClass A]
    (cws : ContractiveWeightSystem A) :
    ∀ (ε : ℝ), 0 < ε →
    ∃ (D : ℕ), ∀ (d : ℕ), D ≤ d → ∀ (l : List A),
      l.length = d → (∀ a ∈ l, a ∈ cws.weights) →
      ‖l.prod‖ < ε := by
  intro ε hε
  -- the largest weight norm `c` is `< 1`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = cws.weights.sup' cws.nonempty (fun a => ‖a‖) := ⟨_, rfl⟩
  have hc1 : c < 1 := by
    rw [hc, Finset.sup'_lt_iff]
    exact cws.contractive
  have hle : ∀ a ∈ cws.weights, ‖a‖ ≤ c := fun a ha => hc ▸ Finset.le_sup' (fun a => ‖a‖) ha
  have hc0 : 0 ≤ c := by
    obtain ⟨a, ha⟩ := cws.nonempty
    exact (norm_nonneg a).trans (hle a ha)
  -- submultiplicativity: `‖∏ l‖ ≤ c ^ |l|`
  have key : ∀ l : List A, (∀ a ∈ l, a ∈ cws.weights) → ‖l.prod‖ ≤ c ^ l.length := by
    intro l
    induction l with
    | nil =>
      intro _
      simp
    | cons a l ih =>
      intro h
      rw [List.prod_cons, List.length_cons, pow_succ]
      calc ‖a * l.prod‖ ≤ ‖a‖ * ‖l.prod‖ := norm_mul_le _ _
        _ ≤ c * c ^ l.length :=
          mul_le_mul (hle a (h a (List.mem_cons_self ..)))
            (ih (fun b hb => h b (List.mem_cons_of_mem _ hb))) (norm_nonneg _) hc0
        _ = c ^ l.length * c := by ring
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hc1
  refine ⟨D, fun d hd l hl hmem => ?_⟩
  calc ‖l.prod‖ ≤ c ^ l.length := key l hmem
    _ = c ^ d := by rw [hl]
    _ ≤ c ^ D := pow_le_pow_of_le_one hc0 hc1.le hd
    _ < ε := hD
