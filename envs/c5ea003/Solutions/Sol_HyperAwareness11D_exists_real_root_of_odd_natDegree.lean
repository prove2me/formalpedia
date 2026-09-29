-- Prove2me | solution 1 for HyperAwareness11D.exists_real_root_of_odd_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:17:18.660345+00:00
-- url     : https://prove2.me/submissions/24edf89e-ba9f-4556-b366-2a5eab70b50e

-- Sol generated from MachineLearning/HyperAwareness11D/SpectralPercept.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Equivariance
import Definitions.Def_MachineLearning_HyperAwareness11D_SpectralPercept

/-!
# Hyper-Awareness V: the parity dividend — every 11-dimensional layer has an invariant percept

Dimension `11` is *odd*, and this file extracts the structural dividend that odd parity pays
to an 11-dimensional perception architecture:

> **Every** linear perception layer on `ℝ¹¹` — with no assumption whatsoever on its weights —
> possesses a nonzero percept direction that it merely rescales.

Equivalently, every `11 × 11` real weight matrix has a real eigenvalue.  This is a genuinely
cross-domain statement: the algebra of the characteristic polynomial meets the topology of
the real line (the intermediate value theorem), and the conclusion fails in even dimensions.

## Main results

* `HyperAwareness11D.exists_real_root_of_odd_natDegree` — a monic real polynomial of odd
  degree has a real root (proved from the asymptotics of polynomials plus the intermediate
  value theorem; Mathlib has no `IsRealClosed ℝ` instance).
* `HyperAwareness11D.exists_real_eigenvector_of_odd` — every real square matrix of odd size
  has a real eigenvalue with a nonzero eigenvector.
* `HyperAwareness11D.exists_invariant_percept_11` — the 11-dimensional statement for
  `linLayer`.
* `HyperAwareness11D.rotation_has_no_invariant_percept` — the *boundary*: in dimension `2`
  the quarter-turn layer has no invariant percept direction, so the result above is a genuine
  consequence of the oddness of `11` and not a formal triviality.
-/

open HyperAwareness11D

open Polynomial Filter Topology

noncomputable section

/-! ## A monic real polynomial of odd degree has a root -/


/-! ## Real eigenvalues in odd dimension -/





/-! ## The boundary: parity is essential -/





open HyperAwareness11D in
theorem solution{p : ℝ[X]} (hmonic : p.Monic)
    (hodd : Odd p.natDegree) : ∃ t : ℝ, p.eval t = 0 := by
  have hdeg0 : p.natDegree ≠ 0 := by
    rcases hodd with ⟨k, hk⟩; omega
  have hdeg : 0 < p.degree := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
    exact_mod_cast Nat.pos_of_ne_zero hdeg0
  have h1 : Tendsto (fun x => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdeg (by simp [hmonic.leadingCoeff])
  obtain ⟨b, hb⟩ := (h1.eventually_ge_atTop 1).exists
  set q : ℝ[X] := p.comp (-X) with hq
  have hqnd : q.natDegree = p.natDegree := by
    simp [hq, Polynomial.natDegree_comp]
  have hqlead : q.leadingCoeff = -1 := by
    rw [hq, Polynomial.leadingCoeff_comp (by simp)]
    simp [hmonic.leadingCoeff, hodd.neg_one_pow]
  have hqdeg : 0 < q.degree := by
    rw [Polynomial.degree_eq_natDegree (fun h => by simp [h] at hqlead), hqnd]
    exact_mod_cast Nat.pos_of_ne_zero hdeg0
  have h2 : Tendsto (fun x => q.eval x) atTop atBot :=
    q.tendsto_atBot_of_leadingCoeff_nonpos hqdeg (by rw [hqlead]; norm_num)
  obtain ⟨c, hc⟩ := (h2.eventually_le_atBot (-1)).exists
  have hcval : p.eval (-c) ≤ -1 := by simpa [hq, Polynomial.eval_comp] using hc
  have hcont : ContinuousOn (fun x => p.eval x) (Set.uIcc (-c) b) :=
    p.continuous_aeval.continuousOn
  have hiv := intermediate_value_uIcc hcont
  have h0 : (0:ℝ) ∈ Set.uIcc (p.eval (-c)) (p.eval b) := by
    rw [Set.mem_uIcc]; left; constructor <;> linarith
  obtain ⟨t, -, ht⟩ := hiv h0
  exact ⟨t, ht⟩
