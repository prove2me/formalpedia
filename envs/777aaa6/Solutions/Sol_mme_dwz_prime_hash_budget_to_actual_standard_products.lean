-- Prove2me | solution 1 for mme_dwz_prime_hash_budget_to_actual_standard_products
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T10:32:10.534899+00:00
-- url     : https://prove2.me/submissions/e0aa7fde-3195-42d5-a59b-2d6f4b2e91dc

import Theorems.Thm_mme_dwz_supported_address_hash_event_counts
import Theorems.Thm_mme_dwz_fourth_many_standard_products_restrict_of_finite_hash_budget
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open MME MME.TensorObj MME.StothersFourth MME.DWZSimultaneous
  MME.DWZComponentRestriction MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.CompleteSplit MME.DWZStep1Support Module PiTensorProduct BigOperators
open scoped Classical
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q N H modulus R k r : ℕ)
    [Fact modulus.Prime] (hq : 0 < q) (hN : 0 < N)
    (I J L : Fin k → Fin 9)
    (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hsum : ∀ c, shape c 0 + shape c 1 + shape c 2 = 8)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ a, mu 2 c a = mu 1 c (Fin.rev a))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ a, mu 2 c a = mu 0 c (Fin.rev a))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N, Supported 8 a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (hinjective : Set.InjOn (owner component shape) (ambient : Set (Fin R)))
    (positions : ∀ a : Fin R, a ∈ targets →
      (Fin N ≃ Σ c, Fin ((p c).length (m c))))
    (hcell : ∀ a (ha : a ∈ targets) c r, component a ((positions a ha).symm ⟨c,r⟩) = c)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (L c).val ∧ (L c).val ≤ a.val + 4)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (modulus / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd modulus)
    (hmodulus : 8 < modulus)
    (degree compatibleDegree : ℕ)
    (hxyBudget : 4 * degree ≤ modulus) (hzBudget : 8 * compatibleDegree ≤ modulus)
    (hx : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 0 = owner component shape a 0)).card ≤ degree)
    (hy : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 1 = owner component shape a 1)).card ≤ degree)
    (hzCard : ∀ a ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape a 2 f ∧ Profile component fourthLeftTag mu a 2 f →
      (targets.filter (fun b ↦ b ≠ a ∧ ZCompatible component shape fourthLeftTag mu b f)).card ≤
        compatibleDegree)
    (hbudget : 8 * modulus ^ 2 * (r * (3 * N + 2)) ≤
      3 * targets.card * S.card) :
    TensorObj.Restrict
      (bigAdd (fun _ : Fin r ↦ kronFin k (fun c ↦ prescribedZPower
        (cwFourthConstituent K q (I c) (J c) (L c))
        (constituentBasis K q (I c) (J c) (L c) 2)
        (fun a : LiftedCoarseCoordinate.{u} q (L c) ↦ cwSquarePairGrade q a.down.val.1)
        (p c) (m c))))
      ((CWObj K q).kronPow (N * 4)) := by
  classical
  have hSr : S ⊆ Finset.range modulus := by
    intro s hs
    exact Finset.mem_range.mpr
      ((Finset.mem_range.mp (hSrange hs)).trans_le (Nat.div_le_self _ _))
  have hasupport : ∀ a ∈ ambient, Supported 8 (owner component shape a) :=
    fun a _ t ↦ hsum (component a t)
  let events := fun a ↦ Finset.univ.filter
    (fun state : (Fin (H + 2) → ZMod modulus) × ZMod modulus ↦
      Retained 8 reindex S state (owner component shape a))
  obtain ⟨hevents, hstates, hsingle, hpair⟩ :=
    mme_dwz_supported_address_hash_event_counts
      N H 8 modulus R hpodd hmodulus reindex S hSr
      (owner component shape) ambient hasupport hinjective
  have hK : S.card * modulus ^ (H + 1) = modulus * (S.card * modulus ^ H) := by
    rw [pow_succ]
    ring
  have hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient, b ≠ a →
      (owner component shape b 0 = owner component shape a 0 ∨
        owner component shape b 1 = owner component shape a 1) →
      (events a ∩ events b).card ≤ S.card * modulus ^ H := by
    intro a ha b hb hba hshare
    apply hpair a (hsub ha) b hb hba.symm
    rcases hshare with hx | hy
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hy.symm⟩
  have hzPair : ∀ a ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape a 2 f ∧ Profile component fourthLeftTag mu a 2 f →
      ∀ b ∈ targets, b ≠ a → ZCompatible component shape fourthLeftTag mu b f →
      (events a ∩ events b).card ≤ S.card * modulus ^ H := by
    intro a ha f hf b hb hba hbf
    apply hpair a (hsub ha) b (hsub hb) hba.symm
    refine ⟨2, ?_⟩
    funext t
    exact (hf.1 t).symm.trans (hbf.1 t)
  have hpow : modulus ^ (H + 3) = modulus ^ 2 * modulus ^ (H + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hfullbudget :
      8 * Fintype.card ((Fin (H + 2) → ZMod modulus) × ZMod modulus) *
        (r * (N * 3 + 2)) ≤ 3 * targets.card * (S.card * modulus ^ (H + 1)) := by
    calc
      _ = (8 * modulus ^ 2 * (r * (3 * N + 2))) * modulus ^ (H + 1) := by
        rw [hstates, hpow]
        ring
      _ ≤ (3 * targets.card * S.card) * modulus ^ (H + 1) :=
        Nat.mul_le_mul_right _ hbudget
      _ = _ := by ring
  exact mme_dwz_fourth_many_standard_products_restrict_of_finite_hash_budget
    (K := K) q N H modulus R k r hq hN I J L p m component shape hshape hsum
    mu hmu hmuX hmuY marginal targets ambient hsub hmarginal hcomplete
    positions hcell hsupport reindex S hSrange hSfree hpodd events hevents
    (S.card * modulus ^ (H + 1)) (S.card * modulus ^ H) degree compatibleDegree
    hK hxyBudget hzBudget (fun a ha ↦ hsingle a (hsub ha)) hx hy hzCard
    hxyPair hzPair hfullbudget
