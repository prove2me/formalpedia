-- Prove2me | solution 1 for CertifiedEvidence.descentCertificate_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:31:50.055891+00:00
-- url     : https://prove2.me/submissions/17298c86-c6be-4c34-94ba-ce5a6aec1437

import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
import Definitions.Def_MachineLearning_CertifiedEvidence_Sufficiency

open CertifiedEvidence

private theorem checkFrom_spec (p : ℕ → Bool) (lo n : ℕ) :
    checkFrom p lo n = true → ∀ t, lo ≤ t → t < lo + n → p t = true := by
  induction n generalizing lo with
  | zero =>
      intro _ t hlo hhi; omega
  | succ n ih =>
      intro h t hlo hhi
      simp only [checkFrom, Bool.and_eq_true] at h
      rcases h with ⟨hp0, hrest⟩
      rcases eq_or_lt_of_le hlo with rfl | hlt
      · exact hp0
      · exact ih (lo + 1) hrest t (by omega) (by omega)

private theorem checkRange_spec (p : ℕ → Bool) (lo hi : ℕ)
    (h : checkRange p lo hi = true) :
    ∀ t, lo ≤ t → t ≤ hi → p t = true := by
  intro t hlo hhi
  unfold checkRange at h
  by_cases hempty : hi < lo
  · omega
  · have hlen : t < lo + (hi + 1 - lo) := by omega
    exact checkFrom_spec p lo (hi + 1 - lo) h t hlo hlen

theorem solution (p : ℕ → Bool) :
    Nonempty (DescentCertificate p) ↔ ∀ n, 1 ≤ n → p n = true := by
  constructor
  · rintro ⟨cert⟩
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hle : n ≤ cert.bound
        · exact checkRange_spec p 1 cert.bound cert.base n hn hle
        · have hlt : cert.bound < n := Nat.lt_of_not_ge hle
          exact cert.step n hlt (ih (cert.reduce n) (cert.reduce_lt n hlt)
            (cert.reduce_pos n hlt))
  · intro hall
    refine ⟨{
      bound := 1
      reduce := fun _ => 1
      base := ?base
      reduce_pos := fun n hn => by omega
      reduce_lt := fun n hn => hn
      step := fun n hn _ => hall n (by omega)
    }⟩
    -- checkRange p 1 1 = true
    have : checkFrom p 1 1 = true := by
      simp [checkFrom, hall 1 (by omega)]
    simpa [checkRange] using this
