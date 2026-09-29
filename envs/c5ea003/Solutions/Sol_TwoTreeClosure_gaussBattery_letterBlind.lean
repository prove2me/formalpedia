-- Prove2me | solution 1 for TwoTreeClosure.gaussBattery_letterBlind
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:47:37.003688+00:00
-- url     : https://prove2.me/submissions/56f4adc7-6e19-4884-bdc0-37fc925540ed

-- Sol generated from Bridges/TwoTreeClosure/GaussDial.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_GaussDial
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_gaussSum_periodic
import Theorems.Thm_TwoTreeClosure_residue_dial_letterBlind

/-!
# Gauss-sum magnitudes are residue dials, hence tree-blind

Strength (2) of the two-tree closure.  A *Gauss-sum probe* at modulus `M` reads

`G_M(N) = ∑_{x < M} exp(2πi x² N / M)`,

and derived probes read any function of `G_M(N)` (for instance its magnitude, its
argument, or a whole vector of such sums at several moduli).

`gaussSum_periodic` proves that `G_M` is invariant under `N ↦ N + M`, hence
`gaussSum_eq_mod` : `G_M(N) = G_M(N mod M)`.  So every Gauss-sum probe *is* a
residue dial, and `gaussProbe_letterBlind` transports the blindness theorem of
`Bridges.TwoTreeClosure.TreeCore` to it: no Gauss-sum probe at any modulus — in
particular none at the smooth modulus `720720` — can output the ascent letter of a
Berggren/Price node.
-/

open TwoTreeClosure

open Finset



/-- A Gauss sum only sees the residue of `N`. -/
theorem gaussSum_eq_mod (M N : ℕ) (hM : 0 < M) : gaussSum M N = gaussSum M (N % M) := by
  conv_lhs => rw [show N = N % M + (N / M) * M from (Nat.mod_add_div' N M).symm]
  exact gaussSum_periodic M (N % M) (N / M) hM





open TwoTreeClosure in
theorem solution(M : ℕ) (hM : 1 ≤ M) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∣ M ∧ 0 < d) (G : (ℕ → ℂ) → Letter) :
    ¬ (∀ m n, IsNode m n → G (fun d => if d ∈ s then gaussSum d (hyp m n) else 0)
        = letterOf m n) := by
  intro hG
  refine residue_dial_letterBlind M hM
    (fun r => G (fun d => if d ∈ s then gaussSum d r else 0)) ?_
  intro m n hmn
  have hfun : (fun d => if d ∈ s then gaussSum d (hyp m n % M) else 0)
      = (fun d => if d ∈ s then gaussSum d (hyp m n) else 0) := by
    funext d
    by_cases hd : d ∈ s
    · simp only [hd, if_true]
      obtain ⟨hdvd, hdpos⟩ := hs d hd
      have hmod : (hyp m n % M) % d = hyp m n % d := Nat.mod_mod_of_dvd _ hdvd
      rw [gaussSum_eq_mod d (hyp m n % M) hdpos, gaussSum_eq_mod d (hyp m n) hdpos, hmod]
    · simp [hd]
  show G (fun d => if d ∈ s then gaussSum d (hyp m n % M) else 0) = letterOf m n
  rw [hfun]
  exact hG m n hmn
