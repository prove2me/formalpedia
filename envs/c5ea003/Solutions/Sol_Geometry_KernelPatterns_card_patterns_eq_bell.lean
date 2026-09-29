-- Prove2me | solution 1 for Geometry.KernelPatterns.card_patterns_eq_bell
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:23:46.778355+00:00
-- url     : https://prove2.me/submissions/a3b6cdc6-3121-4a8e-93de-8d981edc0b32

import Mathlib
import Definitions.Def_Geometry_KernelPatterns_BellRecursion
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling

open Geometry.KernelPatterns Finset in
theorem solution : ∀ n : ℕ, (patterns n n).card = Nat.bell n := by
  classical
  -- partitions of `Fin m` are exactly the patterns of length `m`
  have E : ∀ m, Nat.card (Setoid (Fin m)) = (patterns m m).card := by
    intro m
    let e : Setoid (Fin m) ≃ ↥(patterns m m) :=
      { toFun := fun t => ⟨pat (Quotient.mk t), (mem_patterns_self _).2 (pat_idem _)⟩
        invFun := fun p => Setoid.ker (p : Fin m → Fin m)
        left_inv := fun t => by
          refine Setoid.ext fun a b => ?_
          exact pat_eq_iff.trans Quotient.eq
        right_inv := fun p => by
          apply Subtype.ext
          show pat (Quotient.mk (Setoid.ker (p : Fin m → Fin m))) = p
          exact (pat_congr fun k l => Quotient.eq).trans ((mem_patterns_self _).1 p.2) }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [Nat.bell_zero, Finset.card_eq_one]
      refine ⟨Fin.elim0, ?_⟩
      ext f
      simp only [Finset.mem_singleton]
      constructor
      · intro _; funext i; exact i.elim0
      · rintro rfl
        exact (mem_patterns_self _).2 (funext fun i => i.elim0)
    · have hfib : (patterns (n + 1) (n + 1)).card
          = ∑ S : Finset (Fin n), (lastBlkFibre n S).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := lastBlk) (t := univ)
          (fun p _ => Finset.mem_coe.2 (Finset.mem_univ (lastBlk p)))]
        refine Finset.sum_congr rfl fun S _ => ?_
        unfold lastBlkFibre
        congr 1
      have hS : ∀ S : Finset (Fin n),
          (lastBlkFibre n S).card = (patterns (n - S.card) (n - S.card)).card := by
        intro S
        rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card,
          Nat.card_congr (lastBlkFibreEquiv n S),
          Nat.card_congr (setoidCongr (Fintype.equivFin ↥(Sᶜ))), E,
          Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
      rw [hfib, Finset.sum_congr rfl fun S _ => hS S,
        Finset.sum_congr rfl fun S _ => ih (n - S.card) (by omega),
        ← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun k => Nat.bell (n - k)),
        Finset.card_univ, Fintype.card_fin, Nat.bell_succ,
        Fin.sum_univ_eq_sum_range (fun i => n.choose i * Nat.bell (n - i))]
      simp only [smul_eq_mul]
